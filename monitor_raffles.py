#!/usr/bin/env python3
"""
Gigahertz Giveaways Live Raffle Monitor (`monitor_raffles.py`)
=============================================================
Scrapes active PC competitions from https://gigahertzgiveaways.co.uk/ using a
hybrid REST/AJAX API + HTML DOM scraper (zero external dependencies required):

1. Homepage / Competitions HTML (`https://gigahertzgiveaways.co.uk/`):
   - Extracts active competition product cards (`li.product.product-type-zap_competition`)
   - Parses exact ISO-8601 draw closing timestamps from inline Luxon countdown scripts:
     `DateTime.fromISO("YYYY-MM-DDTHH:MM:SS+00:00", {zone: "Europe/London"})`
   - Parses fallback DOM title (`.woocommerce-loop-product__title`), URL
     (`a.woocommerce-LoopProduct-link`), price (`span.price`), and static ticket
     counts (`.zapc-refresh-sold-<id>`, `.zapc-refresh-max-<id>`).

2. WooCommerce Store REST API (`/wp-json/wc/store/v1/products?include=...`):
   - Retrieves structured pricing in pence (`prices.price`, `prices.regular_price`,
     `prices.sale_price`, `on_sale`) and canonical product titles/permalinks.

3. Zap Competitions Live Uncached MU-Plugin Endpoint
   (`/?zapc-api=ticketData&action=zap_competition_ajax_refresh&ids[]=<id>`):
   - Retrieves real-time uncached `tickets_sold`, `tickets_max`, `tickets_remaining`,
     and `tickets_percentage` for every active competition ID.

Budget & Alerting Logic (£10 Budget + WELCOME10 10% discount -> £11.11 buying power):
- Filters for PC builds containing "5070 Ti", "5080", or "5090" (case-insensitive)
  and excludes multi-PC Instant Win mega comps with `ticket_cap > 20000`.
- `tickets_for_10_gbp = math.floor(10.0 / (ticket_price * 0.90))`
- `live_odds = tickets_for_10_gbp / tickets_sold` (handled safely if `tickets_sold == 0`)
- `max_odds = tickets_for_10_gbp / ticket_cap`
- Sends push notification via POST to `https://ntfy.sh/<NTFY_TOPIC>` if:
  a) A 5070 Ti / 5080 / 5090 draw closes within 4 hours (`0 < hours_remaining <= 4.0`)
     AND `live_odds >= 0.01` (better than 1 in 100), OR
  b) A 5080 / 5090 draw has its active ticket price `< £0.75` with `< 7,000` tickets sold.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass, asdict
from datetime import datetime, timezone
from email.message import EmailMessage
import html
import io
import json
import math
import os
import re
import smtplib
import ssl
import sys
import urllib.error
import urllib.parse
import urllib.request
from typing import Any, Dict, List, Optional, Tuple

# Ensure UTF-8 output on Windows consoles
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

BASE_URL = "https://gigahertzgiveaways.co.uk"
STORE_API_URL = f"{BASE_URL}/wp-json/wc/store/v1/products"
KLAVIYO_FEED_URL = f"{BASE_URL}/wp-json/wc/zap/v1/klaviyo-competition-feed"
TICKET_DATA_API_URL = f"{BASE_URL}/?zapc-api=ticketData"

DEFAULT_HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/130.0.0.0 Safari/537.36"
    ),
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,application/json,*/*;q=0.8",
    "Accept-Language": "en-GB,en;q=0.9",
}

DEFAULT_NTFY_TOPIC = "gigahertz-raffle-b8824aed1ade"
DEFAULT_EMAIL_TO = "teddyprendergast@gmail.com"
TARGET_GPUS = ("5070 Ti", "5080", "5090")
HIGH_TIER_GPUS = ("5080", "5090")
MAX_TICKET_CAP = 20000
BUDGET_GBP = 10.0
DISCOUNT_MULTIPLIER = 0.90  # WELCOME10 (10% off)


@dataclass
class CompetitionData:
    product_id: int
    title: str
    url: str
    gpu_tier: str
    ticket_price: float
    regular_price: float
    sale_price: float
    on_sale: bool
    discounted_price_welcome10: float
    tickets_sold: int
    ticket_cap: int
    tickets_remaining: int
    percent_sold: float
    closing_iso: Optional[str]
    hours_until_close: Optional[float]
    tickets_for_10_gbp: int
    live_odds: Optional[float]
    live_odds_one_in: Optional[float]
    max_odds: float
    max_odds_one_in: Optional[float]
    trigger_a_met: bool
    trigger_b_met: bool
    alert_reasons: List[str]


def http_get(url: str, timeout: int = 20) -> str:
    req = urllib.request.Request(url, headers=DEFAULT_HEADERS)
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read().decode("utf-8", errors="replace")


def http_get_json(url: str, timeout: int = 20) -> Any:
    raw = http_get(url, timeout=timeout)
    return json.loads(raw)


def parse_html_cards(page_html: str) -> Dict[int, Dict[str, Any]]:
    """
    Parses all `<li class="product ... post-<ID> ...">...</li>` cards from the HTML.
    Extracts product_id, title, url, DOM prices, static ticket counts, and Luxon ISO draw date.
    """
    cards: Dict[int, Dict[str, Any]] = {}
    pattern = re.compile(
        r'<li\s+class="[^"]*\bproduct\b[^"]*\bpost-(\d+)\b[^"]*"[^>]*>(.*?)</li>',
        re.DOTALL | re.IGNORECASE,
    )
    for match in pattern.finditer(page_html):
        pid = int(match.group(1))
        body = match.group(2)

        # Title
        title_m = re.search(
            r'<h2\s+class="[^"]*woocommerce-loop-product__title[^"]*"[^>]*>(.*?)</h2>',
            body,
            re.DOTALL | re.IGNORECASE,
        )
        raw_title = html.unescape(re.sub(r"<[^>]+>", "", title_m.group(1)).strip()) if title_m else ""

        # URL
        url_m = re.search(
            r'<a\s+href="(https://gigahertzgiveaways\.co\.uk/competition/[^"]+)"',
            body,
            re.IGNORECASE,
        )
        comp_url = url_m.group(1).strip() if url_m else ""

        # Draw countdown ISO timestamp from Luxon snippet:
        # DateTime.fromISO("2026-10-26T20:00:00+00:00", {zone: "Europe/London"})
        iso_m = re.search(r'DateTime\.fromISO\(\s*["\']([^"\']+)["\']', body)
        closing_iso = iso_m.group(1).strip() if iso_m else None

        # Static sold / max in card HTML
        sold_m = re.search(rf'zapc-refresh-sold-{pid}"[^>]*>\s*([\d,]+)\s*</span>', body)
        max_m = re.search(rf'zapc-refresh-max-{pid}"[^>]*>\s*([\d,]+)\s*</span>', body)
        tickets_sold = int(sold_m.group(1).replace(",", "")) if sold_m else None
        ticket_cap = int(max_m.group(1).replace(",", "")) if max_m else None

        # Price from HTML card (`<span class="price">...</span>`)
        price_block_m = re.search(r'<span\s+class="price"[^>]*>(.*?)</span>\s*<div', body, re.DOTALL)
        price_text = price_block_m.group(1) if price_block_m else body
        # Check for <del> and <ins> if discounted in HTML
        ins_m = re.search(r"<ins[^>]*>.*?&pound;\s*([\d.]+).*?</ins>", price_text, re.DOTALL)
        del_m = re.search(r"<del[^>]*>.*?&pound;\s*([\d.]+).*?</del>", price_text, re.DOTALL)
        all_amounts = re.findall(r"&pound;\s*([\d.]+)", price_text)

        if ins_m and del_m:
            active_price = float(ins_m.group(1))
            reg_price = float(del_m.group(1))
            sale_price = active_price
            on_sale = True
        elif all_amounts:
            active_price = float(all_amounts[-1])
            reg_price = float(all_amounts[0])
            sale_price = active_price
            on_sale = len(all_amounts) > 1 and active_price < reg_price
        else:
            active_price = 0.0
            reg_price = 0.0
            sale_price = 0.0
            on_sale = False

        cards[pid] = {
            "product_id": pid,
            "title": raw_title,
            "url": comp_url,
            "closing_iso": closing_iso,
            "tickets_sold": tickets_sold,
            "ticket_cap": ticket_cap,
            "ticket_price": active_price,
            "regular_price": reg_price,
            "sale_price": sale_price,
            "on_sale": on_sale,
        }

    return cards


def parse_single_competition_page(comp_url: str, pid: int) -> Dict[str, Any]:
    """Fallback parser for an individual competition page if not present on the homepage grid."""
    info: Dict[str, Any] = {}
    try:
        page_html = http_get(comp_url)
    except Exception:
        return info

    iso_m = re.search(r'DateTime\.fromISO\(\s*["\']([^"\']+)["\']', page_html)
    if iso_m:
        info["closing_iso"] = iso_m.group(1).strip()

    sold_m = re.search(rf'zapc-refresh-sold-{pid}"[^>]*>\s*([\d,]+)\s*</span>', page_html)
    max_m = re.search(rf'zapc-refresh-max-{pid}"[^>]*>\s*([\d,]+)\s*</span>', page_html)
    if sold_m:
        info["tickets_sold"] = int(sold_m.group(1).replace(",", ""))
    if max_m:
        info["ticket_cap"] = int(max_m.group(1).replace(",", ""))

    return info


def fetch_live_ticket_counts(product_ids: List[int]) -> Dict[int, Dict[str, Any]]:
    """
    Calls `/?zapc-api=ticketData&action=zap_competition_ajax_refresh&ids[]=<id>`
    to get real-time uncached ticket sales and maximum caps.
    """
    if not product_ids:
        return {}
    params = [("action", "zap_competition_ajax_refresh")]
    for pid in product_ids:
        params.append(("ids[]", str(pid)))
    query = urllib.parse.urlencode(params)
    url = f"{TICKET_DATA_API_URL}&{query}"
    try:
        data = http_get_json(url)
        if isinstance(data, dict):
            return {int(k): v for k, v in data.items() if str(k).isdigit() and isinstance(v, dict)}
    except Exception as exc:
        print(f"[WARN] Live ticketData API fallback to HTML counts ({exc})", file=sys.stderr)
    return {}


def fetch_store_api_products(product_ids: List[int]) -> Dict[int, Dict[str, Any]]:
    """
    Queries `/wp-json/wc/store/v1/products` for the given product IDs (or top 100 active products).
    """
    results: Dict[int, Dict[str, Any]] = {}
    try:
        if product_ids:
            ids_param = ",".join(str(i) for i in product_ids)
            url = f"{STORE_API_URL}?include={ids_param}&per_page=100"
        else:
            url = f"{STORE_API_URL}?per_page=100"
        items = http_get_json(url)
        if isinstance(items, list):
            for item in items:
                pid = int(item["id"])
                prices = item.get("prices", {})
                minor_unit = int(prices.get("currency_minor_unit", 2))
                divisor = 10 ** minor_unit

                raw_price = float(prices.get("price") or 0) / divisor
                raw_reg = float(prices.get("regular_price") or raw_price * divisor) / divisor
                raw_sale = float(prices.get("sale_price") or raw_price * divisor) / divisor
                on_sale = bool(item.get("on_sale")) or (0 < raw_sale < raw_reg)
                active_price = min(p for p in (raw_price, raw_sale) if p > 0) if (raw_price > 0 or raw_sale > 0) else 0.0

                results[pid] = {
                    "product_id": pid,
                    "title": html.unescape(item.get("name", "")).strip(),
                    "url": item.get("permalink", ""),
                    "ticket_price": active_price,
                    "regular_price": raw_reg,
                    "sale_price": raw_sale,
                    "on_sale": on_sale,
                    "type": item.get("type", ""),
                    "is_purchasable": item.get("is_purchasable", True),
                    "is_in_stock": item.get("is_in_stock", True),
                }
    except Exception as exc:
        print(f"[WARN] WooCommerce Store API warning: {exc}", file=sys.stderr)
    return results


def detect_gpu_tier(title: str) -> Optional[str]:
    """Returns the matched GPU tier ('5090', '5080', or '5070 Ti') if found in the title."""
    t_lower = title.lower()
    if "5090" in t_lower:
        return "5090"
    if "5080" in t_lower:
        return "5080"
    if "5070 ti" in t_lower or "5070ti" in t_lower:
        return "5070 Ti"
    return None


def compute_hours_until_close(closing_iso: Optional[str], now_utc: datetime) -> Optional[float]:
    if not closing_iso:
        return None
    try:
        dt = datetime.fromisoformat(closing_iso)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        delta_sec = (dt.astimezone(timezone.utc) - now_utc).total_seconds()
        return round(delta_sec / 3600.0, 2)
    except Exception:
        return None


def scrape_competitions(include_all_filtered_debug: bool = False) -> Tuple[List[CompetitionData], List[Dict[str, Any]]]:
    """
    Scrapes all open competitions, enriches them with Store API + live AJAX ticket data,
    and filters for eligible 5070 Ti / 5080 / 5090 builds (cap <= 20,000).
    Returns `(eligible_competitions, excluded_or_all_raw)`.
    """
    now_utc = datetime.now(timezone.utc)

    # 1. Scrape homepage & /competitions/ HTML cards
    cards: Dict[int, Dict[str, Any]] = {}
    for page_url in (f"{BASE_URL}/", f"{BASE_URL}/competitions/"):
        try:
            page_html = http_get(page_url)
            parsed = parse_html_cards(page_html)
            for pid, cdata in parsed.items():
                if pid not in cards:
                    cards[pid] = cdata
                else:
                    # Merge non-null fields
                    for k, v in cdata.items():
                        if cards[pid].get(k) is None and v is not None:
                            cards[pid][k] = v
        except Exception as exc:
            print(f"[WARN] Failed to fetch {page_url}: {exc}", file=sys.stderr)

    # 2. Check Klaviyo competition feed for any additional open IDs
    feed_ids: List[int] = []
    try:
        feed = http_get_json(KLAVIYO_FEED_URL)
        if isinstance(feed, dict):
            feed_ids = [int(x) for x in (feed.get("open", []) + feed.get("closingsoon", [])) if str(x).isdigit()]
    except Exception:
        pass

    all_candidate_ids = sorted(set(cards.keys()) | set(feed_ids))

    # 3. Fetch WooCommerce Store API product details
    store_products = fetch_store_api_products(all_candidate_ids)

    # Ensure all active IDs found in either HTML or Store API are tracked
    combined_ids = sorted(set(cards.keys()) | set(store_products.keys()))

    # 4. Fetch real-time uncached ticket counts from `/?zapc-api=ticketData`
    live_tickets = fetch_live_ticket_counts(combined_ids)

    eligible: List[CompetitionData] = []
    all_inspected: List[Dict[str, Any]] = []

    for pid in combined_ids:
        c = cards.get(pid, {})
        s = store_products.get(pid, {})
        t = live_tickets.get(pid, {})

        title = s.get("title") or c.get("title") or f"Competition #{pid}"
        comp_url = s.get("url") or c.get("url") or f"{BASE_URL}/?p={pid}"

        # Prefer Store API price if available, but if HTML shows a lower flash sale price, take the minimum positive price
        s_price = s.get("ticket_price", 0.0)
        c_price = c.get("ticket_price", 0.0)
        if s_price > 0 and c_price > 0:
            ticket_price = min(s_price, c_price)
        else:
            ticket_price = s_price or c_price

        regular_price = max(s.get("regular_price", 0.0), c.get("regular_price", 0.0), ticket_price)
        sale_price = min(
            p for p in (s.get("sale_price", 0.0), c.get("sale_price", 0.0), ticket_price) if p > 0
        ) if ticket_price > 0 else 0.0
        on_sale = bool(s.get("on_sale") or c.get("on_sale") or (0 < ticket_price < regular_price))

        # Live ticket counts take priority over static HTML counts
        tickets_sold = t.get("tickets_sold") if t.get("tickets_sold") is not None else c.get("tickets_sold")
        ticket_cap = t.get("tickets_max") if t.get("tickets_max") is not None else c.get("ticket_cap")

        closing_iso = c.get("closing_iso")
        gpu_tier = detect_gpu_tier(title)

        # If it matches a target GPU tier but wasn't on the homepage HTML (missing closing_iso or ticket_cap),
        # fetch its individual competition page once to get the exact Luxon countdown and DOM attributes.
        if gpu_tier and (closing_iso is None or ticket_cap is None) and comp_url:
            single_info = parse_single_competition_page(comp_url, pid)
            if closing_iso is None:
                closing_iso = single_info.get("closing_iso")
            if tickets_sold is None:
                tickets_sold = single_info.get("tickets_sold")
            if ticket_cap is None:
                ticket_cap = single_info.get("ticket_cap")

        tickets_sold_int = int(tickets_sold) if tickets_sold is not None else 0
        ticket_cap_int = int(ticket_cap) if ticket_cap is not None else 0
        tickets_rem_int = (
            int(t["tickets_remaining"])
            if t.get("tickets_remaining") is not None
            else max(0, ticket_cap_int - tickets_sold_int)
        )
        percent_sold = (
            round((tickets_sold_int / ticket_cap_int) * 100.0, 2)
            if ticket_cap_int > 0
            else float(t.get("tickets_percentage", 0.0))
        )

        hours_until_close = compute_hours_until_close(closing_iso, now_utc)

        summary_record = {
            "product_id": pid,
            "title": title,
            "url": comp_url,
            "gpu_tier": gpu_tier,
            "ticket_price": ticket_price,
            "regular_price": regular_price,
            "on_sale": on_sale,
            "tickets_sold": tickets_sold_int,
            "ticket_cap": ticket_cap_int,
            "closing_iso": closing_iso,
            "hours_until_close": hours_until_close,
        }

        if not gpu_tier:
            summary_record["filter_status"] = "Excluded (Not 5070 Ti / 5080 / 5090)"
            all_inspected.append(summary_record)
            continue

        if ticket_cap_int > MAX_TICKET_CAP:
            summary_record["filter_status"] = f"Excluded (Cap {ticket_cap_int:,} > {MAX_TICKET_CAP:,} mega comp)"
            all_inspected.append(summary_record)
            continue

        if ticket_price <= 0 or ticket_cap_int <= 0:
            summary_record["filter_status"] = "Excluded (Free / invalid price or cap)"
            all_inspected.append(summary_record)
            continue

        summary_record["filter_status"] = "Included"
        all_inspected.append(summary_record)

        # Budget & Odds Calculations (£10 budget with WELCOME10 10% discount)
        discounted_price = round(ticket_price * DISCOUNT_MULTIPLIER, 4)
        tickets_for_10_gbp = math.floor(BUDGET_GBP / (ticket_price * DISCOUNT_MULTIPLIER))

        if tickets_sold_int > 0 and tickets_for_10_gbp > 0:
            live_odds: Optional[float] = tickets_for_10_gbp / tickets_sold_int
            live_odds_one_in: Optional[float] = round(1.0 / live_odds, 2)
        elif tickets_sold_int == 0 and tickets_for_10_gbp > 0:
            # When 0 tickets are sold yet, purchasing `tickets_for_10_gbp` tickets gives 100% of the pool (1.0)
            live_odds = 1.0
            live_odds_one_in = 1.0
        else:
            live_odds = 0.0
            live_odds_one_in = None

        max_odds = tickets_for_10_gbp / ticket_cap_int if ticket_cap_int > 0 else 0.0
        max_odds_one_in = round(1.0 / max_odds, 2) if max_odds > 0 else None

        # Trigger (a): A 5070 Ti / 5080 / 5090 draw closes within 4 hours AND live_odds >= 0.01
        trigger_a = (
            gpu_tier in TARGET_GPUS
            and hours_until_close is not None
            and 0.0 < hours_until_close <= 4.0
            and live_odds is not None
            and live_odds >= 0.01
        )

        # Trigger (b): A 5080 / 5090 draw has its ticket price < £0.75 with < 7,000 tickets sold
        trigger_b = (
            gpu_tier in HIGH_TIER_GPUS
            and ticket_price < 0.75
            and tickets_sold_int < 7000
        )

        reasons: List[str] = []
        if trigger_a:
            reasons.append(
                f"Trigger (a): {gpu_tier} closes in {hours_until_close:.2f}h (<= 4h) "
                f"& live_odds={live_odds:.4f} ({live_odds*100:.2f}%, 1 in {live_odds_one_in}) >= 1%"
            )
        if trigger_b:
            reasons.append(
                f"Trigger (b): {gpu_tier} ticket price £{ticket_price:.2f} (< £0.75) "
                f"& tickets_sold={tickets_sold_int:,} (< 7,000)"
            )

        eligible.append(
            CompetitionData(
                product_id=pid,
                title=title,
                url=comp_url,
                gpu_tier=gpu_tier,
                ticket_price=ticket_price,
                regular_price=regular_price,
                sale_price=sale_price,
                on_sale=on_sale,
                discounted_price_welcome10=discounted_price,
                tickets_sold=tickets_sold_int,
                ticket_cap=ticket_cap_int,
                tickets_remaining=tickets_rem_int,
                percent_sold=percent_sold,
                closing_iso=closing_iso,
                hours_until_close=hours_until_close,
                tickets_for_10_gbp=tickets_for_10_gbp,
                live_odds=live_odds,
                live_odds_one_in=live_odds_one_in,
                max_odds=max_odds,
                max_odds_one_in=max_odds_one_in,
                trigger_a_met=trigger_a,
                trigger_b_met=trigger_b,
                alert_reasons=reasons,
            )
        )

    # Sort eligible competitions by hours_until_close ascending
    eligible.sort(key=lambda x: (x.hours_until_close if x.hours_until_close is not None else 999999.0, x.product_id))
    return eligible, all_inspected


def send_ntfy_alert(comp: CompetitionData, topic: str, dry_run: bool = False) -> bool:
    """Sends a POST alert to https://ntfy.sh/<topic>."""
    is_placeholder = not topic or topic in ("<YOUR_CUSTOM_TOPIC>", "YOUR_CUSTOM_TOPIC")
    endpoint = f"https://ntfy.sh/{topic or '<YOUR_CUSTOM_TOPIC>'}"

    odds_pct = f"{comp.live_odds * 100:.2f}%" if comp.live_odds is not None else "N/A"
    max_odds_pct = f"{comp.max_odds * 100:.2f}%"
    body_lines = [
        f"Prize: {comp.title}",
        f"GPU Tier: RTX {comp.gpu_tier}",
        f"Ticket Price: £{comp.ticket_price:.2f} (£{comp.discounted_price_welcome10:.2f} w/ WELCOME10)",
        f"Tickets for £10: {comp.tickets_for_10_gbp} tickets",
        f"Tickets Sold: {comp.tickets_sold:,} / {comp.ticket_cap:,} ({comp.percent_sold:.1f}%)",
        f"Live Odds (£10): {odds_pct} (~1 in {comp.live_odds_one_in})",
        f"Max Odds (£10): {max_odds_pct} (~1 in {comp.max_odds_one_in})",
        f"Closes: {comp.closing_iso} ({comp.hours_until_close}h remaining)",
        f"Triggered By: {'; '.join(comp.alert_reasons)}",
        f"Link: {comp.url}",
    ]
    payload = "\n".join(body_lines).encode("utf-8")

    headers = {
        "Title": f"Gigahertz Raffle Alert: RTX {comp.gpu_tier} ({odds_pct} live odds)",
        "Priority": "high",
        "Tags": "computer,tada,moneybag",
        "Click": comp.url,
    }

    if dry_run or is_placeholder:
        print(f"\n[NTFY DRY-RUN] Would POST to {endpoint}:")
        print(f"  Headers: {headers}")
        print("  Body:\n    " + "\n    ".join(body_lines))
        return False

    req = urllib.request.Request(endpoint, data=payload, headers=headers, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            print(f"[NTFY SENT] Alert POSTed to {endpoint} (HTTP {resp.status}) for {comp.title}")
            return True
    except urllib.error.URLError as exc:
        print(f"[ERROR] Failed to POST alert to {endpoint}: {exc}", file=sys.stderr)
        return False


def format_report_text(eligible: List[CompetitionData], all_inspected: List[Dict[str, Any]]) -> str:
    buf = io.StringIO()
    now_str = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    buf.write("=" * 105 + "\n")
    buf.write(f"GIGAHERTZ GIVEAWAYS RAFFLE MONITOR — {now_str}\n")
    buf.write("Budget: £10.00 | Discount Code: WELCOME10 (10% off -> £11.11 effective buying power)\n")
    buf.write("Filter: RTX 5070 Ti / 5080 / 5090 builds | Max Ticket Cap <= 20,000\n")
    buf.write("=" * 105 + "\n")

    if not eligible:
        buf.write("\nNo active competitions matched the filter criteria.\n")
    else:
        for comp in eligible:
            sale_tag = f" [FLASH SALE from £{comp.regular_price:.2f}]" if comp.on_sale else ""
            alert_tag = "🚨 ALERT TRIGGERED" if (comp.trigger_a_met or comp.trigger_b_met) else "OK (No Alert)"
            live_odds_str = (
                f"{comp.live_odds:.5f} ({comp.live_odds*100:.2f}% | 1 in {comp.live_odds_one_in})"
                if comp.live_odds is not None
                else "N/A"
            )
            max_odds_str = (
                f"{comp.max_odds:.5f} ({comp.max_odds*100:.2f}% | 1 in {comp.max_odds_one_in})"
                if comp.max_odds_one_in is not None
                else "N/A"
            )
            buf.write(f"\n[{comp.product_id}] {comp.title} ({alert_tag})\n")
            buf.write(f"  URL                : {comp.url}\n")
            buf.write(f"  GPU Tier           : RTX {comp.gpu_tier}\n")
            buf.write(
                f"  Ticket Price       : £{comp.ticket_price:.2f}{sale_tag} "
                f"(Effective w/ WELCOME10: £{comp.discounted_price_welcome10:.3f})\n"
            )
            buf.write(f"  Tickets for £10    : {comp.tickets_for_10_gbp} tickets\n")
            buf.write(
                f"  Tickets Sold / Cap : {comp.tickets_sold:,} / {comp.ticket_cap:,} "
                f"({comp.percent_sold:.1f}% sold, {comp.tickets_remaining:,} left)\n"
            )
            buf.write(f"  Draw Closing Date  : {comp.closing_iso} ({comp.hours_until_close} hours remaining)\n")
            buf.write(f"  Live Odds (£10)    : {live_odds_str}\n")
            buf.write(f"  Max Odds (£10)     : {max_odds_str}\n")
            buf.write(
                f"  Alert Checks       : Trigger (a) [<=4h & live_odds>=0.01] = {comp.trigger_a_met} | "
                f"Trigger (b) [5080/5090 <£0.75 & sold<7000] = {comp.trigger_b_met}\n"
            )
            if comp.alert_reasons:
                for r in comp.alert_reasons:
                    buf.write(f"  >>> {r}\n")

    # Show excluded GPU comps (e.g., >20,000 cap mega comps or 5060 Ti builds) for transparency
    excluded_pc = [
        x for x in all_inspected
        if x.get("filter_status") != "Included"
        and re.search(r"\b(?:pc|pcs|5060|5070|5080|5090)\b", x.get("title", ""), re.IGNORECASE)
    ]
    if excluded_pc:
        buf.write("\n" + "-" * 105 + "\n")
        buf.write("Excluded PC / Tech Competitions:\n")
        for ex in excluded_pc:
            buf.write(
                f"  - [{ex['product_id']}] {ex['title']} | "
                f"Price: £{ex['ticket_price']:.2f} | Sold: {ex['tickets_sold']:,}/{ex['ticket_cap']:,} | "
                f"{ex['filter_status']}\n"
            )
    buf.write("=" * 105 + "\n")
    return buf.getvalue()


def format_report_html(eligible: List[CompetitionData], all_inspected: List[Dict[str, Any]]) -> str:
    now_str = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    any_alert = any(c.trigger_a_met or c.trigger_b_met for c in eligible)
    banner_bg = "#dc2626" if any_alert else "#1e293b"
    banner_title = "🚨 GIGAHERTZ RAFFLE ALERT TRIGGERED!" if any_alert else "Gigahertz Giveaways Raffle Report"

    rows_html = []
    for c in eligible:
        is_alert = c.trigger_a_met or c.trigger_b_met
        row_bg = "#fef2f2" if is_alert else "#ffffff"
        status_badge = (
            f'<span style="background:#dc2626;color:#fff;padding:3px 8px;border-radius:4px;font-weight:bold;">'
            f'ALERT: {"; ".join(c.alert_reasons)}</span>'
            if is_alert
            else '<span style="background:#e2e8f0;color:#334155;padding:3px 8px;border-radius:4px;">OK</span>'
        )
        live_odds_str = f"{c.live_odds*100:.2f}% (1 in {c.live_odds_one_in})" if c.live_odds is not None else "N/A"
        max_odds_str = f"{c.max_odds*100:.2f}% (1 in {c.max_odds_one_in})" if c.max_odds_one_in is not None else "N/A"
        rows_html.append(
            f'<tr style="background:{row_bg};border-bottom:1px solid #e2e8f0;">'
            f'<td style="padding:10px;"><a href="{html.escape(c.url)}" style="color:#2563eb;font-weight:600;text-decoration:none;">'
            f'{html.escape(c.title)}</a></td>'
            f'<td style="padding:10px;text-align:center;"><strong>RTX {html.escape(c.gpu_tier)}</strong></td>'
            f'<td style="padding:10px;text-align:right;">£{c.ticket_price:.2f}<br>'
            f'<small style="color:#64748b;">£{c.discounted_price_welcome10:.3f} w/ code</small></td>'
            f'<td style="padding:10px;text-align:center;"><strong>{c.tickets_for_10_gbp}</strong></td>'
            f'<td style="padding:10px;text-align:right;">{c.tickets_sold:,} / {c.ticket_cap:,}<br>'
            f'<small style="color:#64748b;">({c.percent_sold:.1f}%)</small></td>'
            f'<td style="padding:10px;text-align:right;"><strong>{live_odds_str}</strong></td>'
            f'<td style="padding:10px;text-align:right;">{max_odds_str}</td>'
            f'<td style="padding:10px;text-align:right;">{c.hours_until_close}h<br>'
            f'<small style="color:#64748b;">{c.closing_iso or ""}</small></td>'
            f'<td style="padding:10px;text-align:center;">{status_badge}</td>'
            f'</tr>'
        )

    table_body = "\n".join(rows_html) if rows_html else '<tr><td colspan="9" style="padding:16px;text-align:center;">No matching competitions found.</td></tr>'

    return f"""<!DOCTYPE html>
<html>
<body style="font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,sans-serif;color:#0f172a;margin:0;padding:16px;background:#f8fafc;">
  <div style="max-width:960px;margin:0 auto;background:#ffffff;border-radius:8px;overflow:hidden;box-shadow:0 1px 3px rgba(0,0,0,0.1);">
    <div style="background:{banner_bg};color:#ffffff;padding:18px 24px;">
      <h2 style="margin:0;font-size:20px;">{banner_title}</h2>
      <p style="margin:6px 0 0;font-size:13px;opacity:0.85;">{now_str} • £10 Budget (WELCOME10 10% off → £11.11 effective buying power)</p>
    </div>
    <div style="padding:20px;overflow-x:auto;">
      <table style="width:100%;border-collapse:collapse;font-size:13px;">
        <thead>
          <tr style="background:#f1f5f9;color:#475569;text-align:left;border-bottom:2px solid #cbd5e1;">
            <th style="padding:10px;">Competition</th>
            <th style="padding:10px;text-align:center;">GPU</th>
            <th style="padding:10px;text-align:right;">Price</th>
            <th style="padding:10px;text-align:center;">Tix (£10)</th>
            <th style="padding:10px;text-align:right;">Sold / Cap</th>
            <th style="padding:10px;text-align:right;">Live Odds</th>
            <th style="padding:10px;text-align:right;">Max Odds</th>
            <th style="padding:10px;text-align:right;">Closes In</th>
            <th style="padding:10px;text-align:center;">Status</th>
          </tr>
        </thead>
        <tbody>
          {table_body}
        </tbody>
      </table>
    </div>
  </div>
</body>
</html>"""


def send_email_report(
    eligible: List[CompetitionData],
    all_inspected: List[Dict[str, Any]],
    email_to: str,
    dry_run: bool = False,
) -> bool:
    """
    Sends the formatted HTML + plain-text report to `email_to` via Gmail SMTP
    (using EMAIL_USER / EMAIL_APP_PASSWORD environment variables).
    """
    smtp_user = os.environ.get("EMAIL_USER", email_to).strip()
    smtp_password = os.environ.get("EMAIL_APP_PASSWORD", "").strip()
    smtp_host = os.environ.get("SMTP_HOST", "smtp.gmail.com").strip()
    smtp_port = int(os.environ.get("SMTP_PORT", "465"))

    now_str = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    any_alert = any(c.trigger_a_met or c.trigger_b_met for c in eligible)
    subject_prefix = "🚨 [ALERT] " if any_alert else ""
    subject = f"{subject_prefix}Gigahertz Giveaways Raffle Report ({now_str})"

    text_body = format_report_text(eligible, all_inspected)
    html_body = format_report_html(eligible, all_inspected)

    if dry_run or not smtp_password:
        if not smtp_password:
            print(
                f"\n[EMAIL INFO] To send email reports to {email_to}, set EMAIL_APP_PASSWORD "
                f"(Gmail 16-char App Password) in environment / GitHub Secrets.",
                file=sys.stderr,
            )
        return False

    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = f"Gigahertz Raffle Monitor <{smtp_user}>"
    msg["To"] = email_to
    msg.set_content(text_body)
    msg.add_alternative(html_body, subtype="html")

    try:
        context = ssl.create_default_context()
        if smtp_port == 465:
            with smtplib.SMTP_SSL(smtp_host, smtp_port, context=context, timeout=20) as server:
                server.login(smtp_user, smtp_password)
                server.send_message(msg)
        else:
            with smtplib.SMTP(smtp_host, smtp_port, timeout=20) as server:
                server.starttls(context=context)
                server.login(smtp_user, smtp_password)
                server.send_message(msg)
        print(f"[EMAIL SENT] Report emailed to {email_to} via {smtp_host}:{smtp_port}")
        return True
    except Exception as exc:
        print(f"[ERROR] Failed to send email report to {email_to}: {exc}", file=sys.stderr)
        return False


def print_report(eligible: List[CompetitionData], all_inspected: List[Dict[str, Any]]) -> None:
    print(format_report_text(eligible, all_inspected), end="")


def main() -> int:
    parser = argparse.ArgumentParser(description="Monitor Gigahertz Giveaways PC Raffles")
    parser.add_argument(
        "--ntfy-topic",
        default=os.environ.get("NTFY_TOPIC") or DEFAULT_NTFY_TOPIC,
        help=f"ntfy.sh topic name (defaults to NTFY_TOPIC env var or '{DEFAULT_NTFY_TOPIC}')",
    )
    parser.add_argument(
        "--email-to",
        default=os.environ.get("EMAIL_TO") or DEFAULT_EMAIL_TO,
        help=f"Recipient email address for the report (defaults to '{DEFAULT_EMAIL_TO}')",
    )
    parser.add_argument(
        "--no-email",
        action="store_true",
        help="Disable sending the email report",
    )
    parser.add_argument(
        "--ntfy-report",
        action="store_true",
        help="Also POST the full summary report to ntfy.sh on every run",
    )
    parser.add_argument(
        "--json-out",
        default="",
        help="Optional path to write JSON output of scraped competitions",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Do not send live ntfy.sh HTTP requests even if NTFY_TOPIC is set",
    )
    parser.add_argument(
        "--test-alert",
        action="store_true",
        help="Simulate an alert trigger on the best eligible competition to test ntfy payload formatting",
    )
    args = parser.parse_args()

    eligible, all_inspected = scrape_competitions()
    print_report(eligible, all_inspected)

    for comp in eligible:
        if comp.trigger_a_met or comp.trigger_b_met:
            send_ntfy_alert(comp, topic=args.ntfy_topic, dry_run=args.dry_run)

    if not args.no_email and args.email_to:
        send_email_report(eligible, all_inspected, email_to=args.email_to, dry_run=args.dry_run)

    if args.test_alert and eligible:
        sample = eligible[0]
        if not sample.alert_reasons:
            sample.alert_reasons.append("SIMULATED TEST ALERT (--test-alert)")
        send_ntfy_alert(sample, topic=args.ntfy_topic, dry_run=args.dry_run)

    if args.json_out:
        out_data = {
            "timestamp_utc": datetime.now(timezone.utc).isoformat(),
            "budget_gbp": BUDGET_GBP,
            "discount_code": "WELCOME10",
            "effective_buying_power_gbp": round(BUDGET_GBP / DISCOUNT_MULTIPLIER, 2),
            "eligible_competitions": [asdict(c) for c in eligible],
            "all_inspected_competitions": all_inspected,
        }
        with open(args.json_out, "w", encoding="utf-8") as f:
            json.dump(out_data, f, indent=2, ensure_ascii=False)
        print(f"\nSaved JSON report to {args.json_out}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
