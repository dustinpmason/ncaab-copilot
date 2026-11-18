#!/usr/bin/env python3
"""NCAAB Copilot 2.0 engine.

One file, standard library only. Subcommands:

  slate     KenPom FanMatch text + PropLine bulk odds  -> edge board for every game
  build     edge board (+ promo rules)                 -> the best slips, labeled EDGE / FAIR / OVERRIDE
  ladder    PropLine event odds + player game logs     -> overs-only alt-line board
  cover     KenPom margin + win% + spread              -> cover probability
  parlay    legs (+ book price, boost, bonus bet)      -> price, book tax, cash chance, EV
  log       append a placed ticket to the ledger
  settle    record results for a ticket
  audit     ledger -> record, ROI, calibration, CLV, leaks
  selftest  run the built-in checks

Every matcher is fail-closed: anything it cannot pin to exactly one thing is
listed as UNMATCHED instead of being guessed.
"""
import argparse
import csv
import difflib
import json
import math
import os
import re
import statistics
import sys
from statistics import NormalDist

VERSION = "2.2.0"
ND = NormalDist()
BETTABLE = "draftkings,fanduel,betmgm,betonlineag"

# ----------------------------------------------------------------- odds math


def parse_american(x):
    s = str(x).strip().replace("+", "").replace(",", "")
    if s.lower() in ("even", "ev", "pk"):
        return 100.0
    v = float(s)
    if -100 < v < 100:
        raise ValueError(f"not American odds: {x!r}")
    return v


def implied(o):
    o = float(o)
    return -o / (-o + 100) if o < 0 else 100 / (o + 100)


def dec(o):
    o = float(o)
    return 1 + 100 / -o if o < 0 else 1 + o / 100


def american(d):
    if d <= 1:
        return None
    return int(round((d - 1) * 100)) if d >= 2 else int(round(-100 / (d - 1)))


def fmt_am(a):
    if a is None:
        return "n/a"
    a = int(round(a))
    return f"+{a}" if a > 0 else str(a)


def pct(x, nd=1):
    return "n/a" if x is None else f"{100 * x:.{nd}f}%"


def margin_sd(kp_margin, kp_winprob, default=11.0):
    """Back out the game's margin SD from KenPom's own margin and win probability."""
    if kp_margin and kp_margin > 0 and 0.5 < kp_winprob < 0.999:
        sd = kp_margin / ND.inv_cdf(kp_winprob)
        return min(14.0, max(8.0, sd))
    return default


def cover_prob(kp_margin, kp_winprob, spread):
    """P(KenPom's winner covers `spread`), spread as quoted for that team (e.g. -3.5)."""
    sd = margin_sd(kp_margin, kp_winprob)
    return ND.cdf((kp_margin + spread) / sd), sd


# ------------------------------------------------------------------ loading


def load_json(path):
    """Load a PropLine result: raw JSON, JSON after a text preamble, or an MCP
    [{"type":"text","text":"..."}] wrapper."""
    t = open(path, encoding="utf-8", errors="replace").read()
    starts = [i for i in (t.find("{"), t.find("[")) if i >= 0]
    if not starts:
        sys.exit(f"ERROR: no JSON found in {path}")
    d, _ = json.JSONDecoder().raw_decode(t, min(starts))
    if isinstance(d, list) and d and isinstance(d[0], dict) and d[0].get("type") == "text" and "text" in d[0]:
        d = json.loads("".join(x.get("text", "") for x in d))
    return d


# ------------------------------------------------------------ name matching

WORD_MAP = {"state": "st", "saint": "st", "mount": "mt", "university": "", "univ": "", "the": ""}
ALIASES = {
    "uconn": "connecticut", "miami florida": "miami fl", "miami ohio": "miami oh",
    "florida international": "fiu", "fdu": "fairleigh dickinson", "siu edwardsville": "siue",
    "ul monroe": "louisiana monroe", "ulm": "louisiana monroe", "california baptist": "cal baptist",
    "omaha": "nebraska omaha", "ole miss": "mississippi", "st marys ca": "st marys",
    "uic": "illinois chicago", "umkc": "kansas city", "pitt": "pittsburgh", "umass": "massachusetts",
    "ut martin": "tennessee martin", "utsa": "ut san antonio", "sam houston": "sam houston st",
    "southeast missouri st": "southeast missouri", "semo": "southeast missouri",
    "long island": "liu", "long island university": "liu", "byu": "brigham young", "usc": "southern california",
    "ucf": "central florida", "smu": "southern methodist", "vcu": "virginia commonwealth",
    "unlv": "nevada las vegas", "lsu": "louisiana st", "tcu": "texas christian",
    "uab": "alabama birmingham", "utep": "texas el paso", "csun": "cal st northridge",
    "app st": "appalachian st", "nc st": "north carolina st", "n c st": "north carolina st",
    "unc": "north carolina", "ut arlington": "texas arlington", "ut rio grande valley": "texas rio grande valley",
    "siu": "southern illinois", "etsu": "east tennessee st", "mtsu": "middle tennessee",
    "middle tennessee st": "middle tennessee", "umbc": "maryland baltimore county",
    "penn": "pennsylvania", "st johns ny": "st johns", "loyola il": "loyola chicago",
    "texas a and m cc": "texas a and m corpus christi", "a and m corpus christi": "texas a and m corpus christi",
    "texas a and m corpus chris": "texas a and m corpus christi", "albany ny": "albany",
    "ualbany": "albany", "college of charleston": "charleston",
    "nj tech": "njit",
    "grambling": "grambling st", "st francis pa": "st francis", "queens nc": "queens",
    "cal st bakersfield": "cal st bakersfield", "csu bakersfield": "cal st bakersfield",
    "csu fullerton": "cal st fullerton", "csu northridge": "cal st northridge",
    "ark pine bluff": "arkansas pine bluff", "mississippi valley": "mississippi valley st",
    "nicholls st": "nicholls", "mcneese st": "mcneese", "se louisiana": "southeastern louisiana",
    "louisiana lafayette": "louisiana", "ul lafayette": "louisiana", "texas a and m commerce": "east texas a and m",
    "nc greensboro": "unc greensboro", "nc wilmington": "unc wilmington", "nc asheville": "unc asheville",
    "uncw": "unc wilmington", "north carolina wilmington": "unc wilmington", "uncg": "unc greensboro",
    "north carolina greensboro": "unc greensboro", "unca": "unc asheville", "north carolina asheville": "unc asheville",
    "iupui": "iu indy", "loyola maryland": "loyola md", "st thomas mn": "st thomas",
    "massachusetts lowell": "umass lowell", "arkansas little rock": "little rock", "fort wayne": "purdue fort wayne",
    "ipfw": "purdue fort wayne", "detroit": "detroit mercy", "se missouri st": "southeast missouri",
    "central connecticut st": "central connecticut", "prairie view": "prairie view a and m",
    "nc a and t": "north carolina a and t", "nc central": "north carolina central",
    "south carolina upstate": "usc upstate", "umes": "maryland eastern shore", "md eastern shore": "maryland eastern shore",
}


MASCOT_WORDS = set("""
aces aggies anteaters antelopes lopes aztecs badgers bearcats bearkats bears beavers bengals big billikens bison
black blazers blue bluejays bobcats boilermakers bonnies braves broncos broncs bruins buccaneers buckeyes buffaloes
bulldogs bulls camels cardinal cardinals catamounts cavaliers chanticleers chippewas colonels colonials commodores
cornhuskers cougars cowboys coyotes crimson crusaders cyclones danes deacons delta demon demons devils dolphins dons
dragons ducks dukes eagles explorers falcons fighting flames flashes flyers foxes friars frogs gaels gators gauchos
golden gophers governors great green griffins grizzlies hatters hawkeyes hawks heels hens herd highlanders hilltoppers
hokies hoosiers horned hornets hoyas hurricane hurricanes huskies illini irish islanders jackets jackrabbits jaguars
jaspers jayhawks jays keydets knights lakers lancers leathernecks lions lobos longhorns lumberjacks mastodons matadors
mavericks mean midshipmen miners minutemen mocs monarchs mountaineers musketeers mustangs nittany norse orange ospreys
owls pack paladins panthers patriots peacocks penguins phoenix pilots pioneers pirates privateers pride purple quakers
racers ragin cajuns raiders ramblers rams rattlers razorbacks rebels red redbirds redhawks retrievers revolutionaries
river roadrunners rockets roos royals runnin salukis scarlet seahawks seawolves seminoles sharks shockers skyhawks
sooners spartans spiders stags storm sun sycamores tar terrapins terriers texans thunderbirds thundering tide tigers
titans toreros trailblazers tribe tritons trojans utes vandals vaqueros vikings volunteers warhawks warriors wave
waves wildcats wolf wolfpack wolverines wolves yellow zags zips 49ers
""".split())


def norm_team(name, extra=None):
    s = name.lower().replace("&", " and ").replace("-", " ")
    s = re.sub(r"[.'\u2019()]", "", s)
    words = [WORD_MAP.get(w, w) for w in s.split()]
    s = " ".join(w for w in words if w)
    table = dict(ALIASES)
    if extra:
        table.update(extra)
    if s in table:
        return table[s]
    toks = s.split()                       # strip a trailing mascot: "bryant bulldogs" -> "bryant"
    while len(toks) > 1 and toks[-1] in MASCOT_WORDS:
        toks = toks[:-1]
    stem = " ".join(toks)
    return table.get(stem, stem) if stem != s else s


def raw_norm(name):
    s = name.lower().replace("&", " and ").replace("-", " ")
    s = re.sub(r"[.'\u2019()]", "", s)
    return " ".join(w for w in (WORD_MAP.get(w, w) for w in s.split()) if w)


def team_sim(a, b, extra=None):
    """1.0 = same school; 0.85 = same after dropping a mascot; else a strict near-identical check."""
    table = dict(ALIASES)
    if extra:
        table.update(extra)
    ra, rb = raw_norm(a), raw_norm(b)
    if table.get(ra, ra) == table.get(rb, rb):
        return 1.0
    if norm_team(a, extra) == norm_team(b, extra):
        return 0.85
    return difflib.SequenceMatcher(None, ra, rb).ratio() * 0.85


# ---------------------------------------------------------- FanMatch parsing

FM_RE = re.compile(
    r"(?P<ar>\d+|NR)\s+(?P<away>[^\n]+?)\s+(?P<loc>at|vs\.)\s+(?P<hr>\d+|NR)\s+(?P<head>[^\n]+?)\s+"
    r"(?P<s1>\d+)-(?P<s2>\d+)\s+\((?P<p>[\d.]+)%\)\s+\[(?P<tempo>\d+)\]"
)


def parse_fanmatch(text):
    """Parse the text of kenpom.com/fanmatch.php. Returns (games, unparsed).

    Accepts the page text as copied (two-line 'A at' / 'B<TAB>Winner 83-76 (73%) [72]' rows)
    or one game per line as CSV: away,home,winner,winner_pts,loser_pts,win_pct[,N for neutral]."""
    games, bad = [], []
    for line in text.splitlines():
        if line.count(",") >= 5 and "(" not in line:
            f = [x.strip() for x in line.split(",")]
            try:
                games.append(dict(away=f[0], home=f[1], winner=f[2], sw=int(f[3]), sl=int(f[4]),
                                  p=float(f[5]) / 100, neutral=len(f) > 6 and f[6].upper().startswith("N"),
                                  tempo=None))
            except (ValueError, IndexError):
                bad.append(line.strip())
    joined = re.sub(r"[ \t]+(at|vs\.)[ \t]*\n[ \t]*", r" \1 ", text)
    for line in joined.splitlines():
        m = FM_RE.search(line)
        if not m:
            continue
        away, head = m["away"].strip(), m["head"].strip()
        home = winner = None
        if "\t" in head:
            parts = [x.strip() for x in head.split("\t") if x.strip()]
            if len(parts) == 2:
                home, winner = parts
        if home is None:
            w = head.split()
            if len(w) % 2 == 0 and w[: len(w) // 2] == w[len(w) // 2:]:
                home = winner = " ".join(w[: len(w) // 2])
            elif head.endswith(away) and len(head) > len(away):
                home, winner = head[: -len(away)].strip(), away
        if not home or winner not in (away, home):
            bad.append(line.strip()[:120])
            continue
        games.append(dict(away=away, home=home, winner=winner, sw=int(m["s1"]), sl=int(m["s2"]),
                          p=float(m["p"]) / 100, neutral=m["loc"] == "vs.", tempo=int(m["tempo"])))
    return games, bad


# ------------------------------------------------------------- slate command


def _side_of(o, ev):
    """Which side an outcome is: the book's own `side` field, else a strict name match."""
    sd = (o.get("side") or "").lower()
    if sd in ("home", "away"):
        return sd
    name = o.get("name") or ""
    h, w = team_sim(name, ev["home_team"]), team_sim(name, ev["away_team"])
    if max(h, w) >= 0.85 and h != w:
        return "home" if h > w else "away"
    return None


def _event_lines(ev):
    """Per book: main moneyline and main spread, keyed by side ('home'/'away').

    Books spell teams differently from the event ("Gonzaga Bulldogs", "NC State Wolfpack"),
    so outcomes are pinned by side, never by name."""
    out = {}
    for b in ev.get("bookmakers") or []:
        if ev.get("live") and b.get("pregame_only"):
            continue
        rec = {}
        for m in b.get("markets") or []:
            if m.get("suspended_at") or m.get("line_type") not in (None, "main") or m.get("period"):
                continue
            if m["key"] not in ("h2h", "spreads") or len(m.get("outcomes") or []) != 2:
                continue
            sides = [_side_of(o, ev) for o in m["outcomes"]]
            if set(sides) != {"home", "away"} or any(o.get("price") is None for o in m["outcomes"]):
                continue
            by = dict(zip(sides, m["outcomes"]))
            if m["key"] == "h2h" and "ml" not in rec:
                x, y = implied(by["home"]["price"]), implied(by["away"]["price"])
                rec["ml"] = {k: by[k]["price"] for k in by}
                rec["nv"] = {"home": x / (x + y), "away": y / (x + y)}
            elif m["key"] == "spreads" and "sp" not in rec:
                if all(o.get("point") is not None for o in m["outcomes"]):
                    rec["sp"] = {k: (by[k]["point"], by[k]["price"]) for k in by}
        if rec:
            out[b["key"]] = rec
    return out


def match_games(games, events, extra=None, threshold=0.8):
    """Pin each KenPom game to one PropLine event. Returns (matched, unmatched)."""
    matched, unmatched = [], []
    for g in games:
        cands = []
        for ev in events:
            s1 = (team_sim(g["away"], ev["away_team"], extra), team_sim(g["home"], ev["home_team"], extra))
            s2 = (team_sim(g["away"], ev["home_team"], extra), team_sim(g["home"], ev["away_team"], extra))
            for s, swapped in ((s1, False), (s2, True)):
                if min(s) >= threshold:
                    cands.append((sum(s), len(_event_lines(ev)), ev, swapped))
        if not cands:
            unmatched.append((g, "no PropLine event with both teams"))
            continue
        cands.sort(key=lambda c: (c[0], c[1]), reverse=True)
        best = cands[0]
        key = lambda ev: frozenset((norm_team(ev["away_team"], extra), norm_team(ev["home_team"], extra)))
        rivals = [c for c in cands[1:] if key(c[2]) != key(best[2]) and best[0] - c[0] < 0.1]
        if rivals:
            unmatched.append((g, "ambiguous: " + " / ".join(
                f"{c[2]['away_team']} @ {c[2]['home_team']}" for c in [best] + rivals)))
            continue
        ev, swapped = best[2], best[3]
        names = {g["away"]: ev["home_team"] if swapped else ev["away_team"],
                 g["home"]: ev["away_team"] if swapped else ev["home_team"]}
        sides = {g["away"]: "home" if swapped else "away", g["home"]: "away" if swapped else "home"}
        matched.append((g, ev, names, sides))
    return matched, unmatched


KP_NUDGE_UP, KP_NUDGE_DOWN = 0.02, 0.03


def working_prob(kp_p, mk_p, kp_weight):
    """The market's no-vig probability, nudged toward KenPom by at most +2 / -3 points.

    The market is the anchor. The shortlist is built from games where KenPom is most
    optimistic, so an uncapped blend overstates every leg picked (seen on 14 Nov, when the
    copilot's legs ran 2 to 8 points above the sharp closing line)."""
    return mk_p + max(-KP_NUDGE_DOWN, min(KP_NUDGE_UP, kp_weight * (kp_p - mk_p)))


def teams_in_fanmatch(text):
    """Normalized names of every team on a FanMatch page, finished games included."""
    games, _ = parse_fanmatch(text)
    names = {g["away"] for g in games} | {g["home"] for g in games}
    lines = text.splitlines()
    for i, line in enumerate(lines[:-1]):
        m1 = re.match(r"^\s*(?:\d+|NR)\s+(.+?)\s+(\d+),\s*$", line)
        m2 = re.match(r"^\s*(?:\d+|NR)\s+(.+?)\s+(\d+)\s*(?:\[\d+\])?", lines[i + 1])
        if m1 and m2:
            names |= {m1[1], m2[1]}
    return {norm_team(n) for n in names}


def build_board(games, events, books=BETTABLE, kp_weight=0.5, extra=None, played_yesterday=None):
    books = [b.strip() for b in books.split(",") if b.strip()]
    played_yesterday = played_yesterday or set()
    matched, unmatched = match_games(games, events, extra)
    rows = []
    for g, ev, names, sides in matched:
        lines = _event_lines(ev)
        pick_side = sides[g["winner"]]
        loser = g["home"] if g["winner"] == g["away"] else g["away"]
        nv = [r["nv"][pick_side] for r in lines.values() if "nv" in r]
        mk_pick = statistics.median(nv) if nv else None
        # The play is the side with the higher working probability, which is not always KenPom's pick.
        play, opp, side, kp_p, kp_margin, flipped = g["winner"], loser, pick_side, g["p"], g["sw"] - g["sl"], False
        if mk_pick is not None and (working_prob(1 - g["p"], 1 - mk_pick, kp_weight)
                                    > working_prob(g["p"], mk_pick, kp_weight)):
            play, opp, side, flipped = loser, g["winner"], ("away" if pick_side == "home" else "home"), True
            kp_p, kp_margin = 1 - g["p"], -(g["sw"] - g["sl"])
        mk_p = None if mk_pick is None else (1 - mk_pick if flipped else mk_pick)
        work = None if mk_p is None else working_prob(kp_p, mk_p, kp_weight)
        sp = [r["sp"][side][0] for r in lines.values() if "sp" in r]
        mk_sp = statistics.median(sp) if sp else None
        prices = {b: r["ml"][side] for b, r in lines.items() if "ml" in r}
        best_ml = None
        for b in books:
            if b in prices and (best_ml is None or dec(prices[b]) > dec(best_ml[0])):
                best_ml = (prices[b], b)
        best_sp = None
        for b in books:
            r = lines.get(b)
            if r and "sp" in r:
                pt, pr = r["sp"][side]
                if best_sp is None or (pt, dec(pr)) > (best_sp[0], dec(best_sp[1])):
                    best_sp = (pt, pr, b)
        row = dict(
            game=f"{g['away']} {'vs' if g['neutral'] else '@'} {g['home']}", event_id=ev["id"],
            play=play, opponent=opp, propline_name=names[play], side=side, kp_pick=g["winner"],
            kp_score=f"{g['sw']}-{g['sl']}", kp_margin=kp_margin, kp_p=kp_p, mk_p=mk_p, ml_books=len(nv),
            edge_pp=None if mk_p is None else 100 * (kp_p - mk_p), work_p=work, mk_spread=mk_sp,
            spread_edge=None if mk_sp is None else kp_margin + mk_sp, prices=prices, best_ml=best_ml,
            best_spread=best_sp, live=bool(ev.get("live")), commence=ev.get("commence_time"), flags=[],
        )
        if best_ml and work is not None:
            row["mkt_ev"] = mk_p * dec(best_ml[0]) - 1
            row["work_ev"] = work * dec(best_ml[0]) - 1
        if best_sp:
            cp, sd = cover_prob(kp_margin, kp_p, best_sp[0])
            row["kp_cover"] = cp
            row["blend_cover"] = kp_weight * cp + (1 - kp_weight) * 0.5
        f = row["flags"]
        if row["live"]:
            f.append("LIVE")
        if mk_p is None:
            f.append("NO-ML")
        else:
            if best_ml and best_ml[0] < -400:
                f.append("CHALK")
            elif best_ml and work >= 0.60 and not row["live"]:
                f.append("ANCHOR")
            if row.get("mkt_ev", -1) >= 0 and not row["live"]:
                f.append("VALUE")
            if flipped or mk_pick < 0.5:
                f.append("KP-VS-MKT")
            elif row["edge_pp"] >= 2:
                f.append("KP+")
            elif row["edge_pp"] <= -5:
                f.append("KP-")
        if mk_sp is not None and -8.5 <= mk_sp <= -6.5:
            f.append("LEAK-BAND")
        if g["neutral"]:
            f.append("NEUTRAL")
        elif sides[g["home"]] == "away":
            f.append("SITE?")
        if norm_team(play, extra) in played_yesterday:
            f.append("B2B")
        if norm_team(opp, extra) in played_yesterday:
            f.append("OPP-B2B")
        rows.append(row)
    rows.sort(key=lambda r: (r["live"], r.get("work_ev") is None, -(r.get("work_ev") or 0)))
    return rows, unmatched


def et_time(iso):
    """'2026-11-14T20:30:00Z' -> (minutes after midnight ET, '3:30 PM')."""
    if not iso:
        return None, ""
    import datetime
    try:
        t = datetime.datetime.strptime(iso[:19], "%Y-%m-%dT%H:%M:%S").replace(tzinfo=datetime.timezone.utc)
    except ValueError:
        return None, ""
    try:
        from zoneinfo import ZoneInfo
        t = t.astimezone(ZoneInfo("America/New_York"))
    except Exception:
        t = t.astimezone(datetime.timezone(datetime.timedelta(hours=-5)))
    return t.hour * 60 + t.minute, t.strftime("%I:%M %p").lstrip("0")


def cmd_slate(a):
    text = open(a.fanmatch, encoding="utf-8", errors="replace").read()
    games, bad = parse_fanmatch(text)
    events = load_json(a.odds)
    if isinstance(events, dict):
        events = [events]
    extra = {}
    for al in a.alias or []:
        k, v = al.split("=", 1)
        extra[norm_team(k)] = norm_team(v)
    prev = set()
    if a.prev_fanmatch:
        prev = teams_in_fanmatch(open(a.prev_fanmatch, encoding="utf-8", errors="replace").read())
    rows, unmatched = build_board(games, events, a.books, a.kp_weight, extra, prev)
    print(f"NCAAB edge board  |  KenPom games parsed: {len(games)}  matched to odds: {len(rows)}  "
          f"unmatched: {len(unmatched)}  unparsed lines: {len(bad)}  |  KenPom weight: {a.kp_weight}"
          + ("" if a.prev_fanmatch else "  |  no --prev-fanmatch given, so rest is NOT checked"))
    hdr = f"{'Game':36} {'Play':19} {'Tip ET':>8} {'KP%':>4} {'Mkt%':>4} {'Edge':>6} {'Work':>5} " \
          f"{'Best ML':>15} {'MktEV':>6} {'WkEV':>6} {'Sprd':>6}  Flags"
    print(hdr)
    print("-" * len(hdr))

    def cell(v, fmt, suffix=""):
        return "" if v is None else format(v, fmt) + suffix

    hidden_live = 0
    for r in rows:
        if r["live"] and not a.include_live:
            hidden_live += 1
            continue
        if a.min_work is not None and (r["work_p"] is None or 100 * r["work_p"] < a.min_work):
            continue
        if a.min_edge is not None and (r["edge_pp"] is None or r["edge_pp"] < a.min_edge):
            continue
        bm = fmt_am(r["best_ml"][0]) + " " + r["best_ml"][1][:10] if r["best_ml"] else "n/a"
        cols = [
            r["game"][:36].ljust(36), r["play"][:19].ljust(19), et_time(r["commence"])[1].rjust(8),
            cell(100 * r["kp_p"], ".0f").rjust(4),
            cell(None if r["mk_p"] is None else 100 * r["mk_p"], ".0f").rjust(4),
            cell(r["edge_pp"], "+.1f").rjust(6),
            cell(None if r["work_p"] is None else 100 * r["work_p"], ".0f", "%").rjust(5), bm.rjust(15),
            cell(100 * r["mkt_ev"] if "mkt_ev" in r else None, "+.1f", "%").rjust(6),
            cell(100 * r["work_ev"] if "work_ev" in r else None, "+.1f", "%").rjust(6),
            cell(r["mk_spread"], "+.1f").rjust(6), " " + ",".join(r["flags"]),
        ]
        print(" ".join(cols))
    if hidden_live:
        print(f"\n{hidden_live} games already in progress are hidden (their odds are in-play, so a pregame "
              "comparison would be wrong). Pass --include-live to list them.")
    print("\nPlay = the side with the higher working probability. Mkt% = the market's no-vig win probability "
          "(median across books). Edge = KenPom minus market, in points. Work = the market, nudged toward "
          "KenPom by at most +2 / -3 points. MktEV = best price against the market's fair number; WkEV = "
          "against Work.")
    if unmatched:
        print("\nUNMATCHED (not guessed - resolve by hand or pass --alias 'KenPom name=PropLine name'):")
        for g, why in unmatched:
            print(f"  {g['away']} {'vs' if g['neutral'] else '@'} {g['home']}: {why}")
    if bad:
        print("\nUNPARSED FanMatch lines:")
        for b in bad:
            print("  " + b)
    if a.json:
        json.dump(rows, open(a.json, "w"), indent=1, default=str)
        print(f"\nBoard saved to {a.json}")


# ------------------------------------------------------------- build command


def _hhmm(s):
    h, m = s.split(":")
    return int(h) * 60 + int(m)


def find_slips(rows, books, min_legs, max_legs, min_prob, min_odds, boost, stake, bonus, top, overlap,
               max_candidates=28, worst_leg=-400):
    """Every qualifying single-book slip, best chance to cash first. Returns a list of dicts."""
    cands = [r for r in rows if r.get("work_p") is not None and r["work_p"] >= min_prob]
    cands.sort(key=lambda r: -r["work_p"])
    cands = cands[:max_candidates]
    priced_books = {b for r in rows for b in (r.get("prices") or {})}
    if any(b in priced_books for b in books):          # reference pricing only when no carried book was asked for
        books = [b for b in books if b in priced_books]
    need = dec(parse_american(min_odds)) if min_odds else None
    out = []
    import itertools
    for b in books:
        ref = b not in priced_books                     # a book PropLine does not carry: use best-of prices
        legs_b = []
        for r in cands:
            if ref:
                pr = r["best_ml"][0] if r.get("best_ml") else None
            else:
                pr = (r.get("prices") or {}).get(b)
            if pr is not None and pr >= worst_leg:
                legs_b.append((r, pr))
        for n in range(min_legs, max_legs + 1):
            for combo in itertools.combinations(legs_b, n):
                d = math.prod(dec(pr) for _, pr in combo)
                if need and d < need - 1e-9:
                    continue
                cash = math.prod(r["work_p"] for r, _ in combo)
                mcash = math.prod(r["mk_p"] for r, _ in combo)
                profit = stake * (d - 1) * (1 + boost)
                ev = cash * profit if bonus else cash * profit - (1 - cash) * stake
                mev = mcash * profit if bonus else mcash * profit - (1 - mcash) * stake
                out.append(dict(book=b, ref=ref, legs=combo, dec=d, cash=cash, profit=profit, ev=ev, mcash=mcash, mev=mev,
                                breakeven=None if bonus else stake / (stake + profit)))
    out.sort(key=lambda s: (-s["cash"], -s["ev"]))
    picked, used = [], set()
    for s in out:
        games = {r["game"] for r, _ in s["legs"]}
        if not overlap and games & used:
            continue
        picked.append(s)
        used |= games
        if len(picked) >= top:
            break
    return picked


def print_slip(i, s, label, stake, boost, bonus, why=""):
    d = s["dec"]
    price = fmt_am(american(d))
    boosted = f" -> boosted {fmt_am(american(1 + (d - 1) * (1 + boost)))}" if boost else ""
    book = s["book"] + (" (reference prices: best of the books PropLine carries)" if s["ref"] else "")
    be = "" if s["breakeven"] is None else f" (break-even {pct(s['breakeven'])})"
    back = s["profit"] if bonus else s["profit"] + stake
    print(f"\n#{i}  {label}  |  {book}  |  {price}{boosted}  |  ${stake:g} returns ${back:.2f}")
    print(f"    Chance to cash: {pct(s['mcash'])} at the market's probabilities, {pct(s['cash'])} at working "
          f"probabilities{be}")
    print(f"    EV: ${s['mev']:+.2f} ({s['mev'] / stake:+.0%}) at the market's probabilities, "
          f"${s['ev']:+.2f} ({s['ev'] / stake:+.0%}) at working probabilities")
    if why:
        print(f"    {why}")
    for r, pr in s["legs"]:
        print(f"    {r['play'][:22]:22} ML {fmt_am(pr):>5}  work {pct(r['work_p'], 0):>4}  mkt {pct(r['mk_p'], 0):>4}  "
              f"KenPom {pct(r['kp_p'], 0):>4}  {et_time(r['commence'])[1]:>8} ET  "
              f"[event {r['event_id']}] {','.join(r['flags'])}")


def cmd_build(a):
    rows = json.load(open(a.board))
    books = [b.strip() for b in a.books.split(",") if b.strip()]
    lo = _hhmm(a.tip_from) if a.tip_from else None
    hi = _hhmm(a.tip_to) if a.tip_to else None
    skip = [x.strip().lower() for x in (a.exclude or "").split(",") if x.strip()]
    pool = []
    for r in rows:
        if r.get("live"):
            continue
        mins = et_time(r.get("commence"))[0]
        if lo is not None and (mins is None or mins < lo):
            continue
        if hi is not None and (mins is None or mins > hi):
            continue
        if any(x in r["game"].lower() for x in skip):
            continue
        pool.append(r)
    boost = a.boost / 100
    promo = bool(a.min_odds or a.boost)
    # A promo minimum such as +400 cannot be reached with three 60% legs (three -160s make about +330),
    # so promo slips get a 55% bar and up to four legs. Everything else keeps 60% and three.
    relaxed = bool(a.min_odds and (a.boost or a.bonus))
    if a.min_prob is None:
        a.min_prob = 0.55 if relaxed else 0.60
    if a.max_legs is None:
        a.max_legs = 4 if relaxed else 3
    print(f"Slip builder  |  {len(pool)} games in the window  |  books: {','.join(books)}  |  "
          f"legs {a.min_legs}-{a.max_legs}  |  leg bar {a.min_prob:.0%}"
          + (f"  |  minimum {a.min_odds}" if a.min_odds else "") + (f"  |  boost {a.boost:g}%" if a.boost else "")
          + ("  |  bonus bet" if a.bonus else ""))
    n = 0
    if not a.override_only:
        slips = find_slips(pool, books, a.min_legs, a.max_legs, a.min_prob, a.min_odds, boost, a.stake, a.bonus,
                           a.top, a.allow_overlap, worst_leg=a.worst_leg)
        for s in slips:
            n += 1
            print_slip(n, s, "BONUS" if a.bonus else ("EDGE" if s["mev"] >= 0 else "FAIR"), a.stake, boost, a.bonus)
    if n == 0:
        if not a.override_only:
            print("\nNo slip inside the rules meets this promo. Two options follow.")
        if promo and not a.override_only:
            alt = find_slips(pool, books, 2, 3, a.min_prob, "+100", 0.0, a.stake, False, 1, True, worst_leg=a.worst_leg)
            for s in alt:
                n += 1
                print_slip(n, s, "EDGE" if s["mev"] >= 0 else "FAIR", a.stake, 0.0, False,
                           "Best slip inside the rules, without the promo.")
        ov = find_slips(pool, books, a.min_legs, max(a.max_legs, 4), 0.45, a.min_odds, boost,
                        a.stake, a.bonus, 1, True, worst_leg=a.worst_leg)
        for s in ov:
            n += 1
            broken = []
            weak = [r["play"] for r, _ in s["legs"] if r["work_p"] < a.min_prob]
            if weak:
                broken.append("leg under the bar: " + ", ".join(weak))
            if len(s["legs"]) > a.max_legs:
                broken.append(f"{len(s['legs'])} legs")
            print_slip(n, s, "OVERRIDE", a.stake, boost, a.bonus,
                       "Meets the promo by breaking a rule (" + "; ".join(broken or ["relaxed search"]) + "). "
                       "Only if Dustin asks for it.")
    if n == 0:
        print("\nNothing can be built from this window. Widen the tip window or add books.")
    print("\nEDGE = clears break-even at the market's own probabilities, so it does not depend on KenPom being "
          "right. FAIR = a sound slip at a fair price, no edge. OVERRIDE = breaks a rule to meet the promo. "
          "Chance to cash treats legs as independent. "
          "Flags to act on before recommending: B2B, SITE?, NEUTRAL, KP-, KP-VS-MKT. Movement and "
          "availability are not checked here.")


# ------------------------------------------------------------ ladder command

STAT_KEYS = {
    "player_points": "points", "player_rebounds": "rebounds", "player_assists": "assists",
    "player_threes": "threes", "player_points_rebounds_assists": "pra", "player_points_rebounds": "pr",
    "player_points_assists": "pa", "player_rebounds_assists": "ra", "player_steals": "steals",
    "player_blocks": "blocks", "player_turnovers": "turnovers", "player_blocks_steals": "stocks",
}


def norm_player(n):
    n = n.strip()
    n = re.sub(r"\s*\([A-Za-z&. ]+\)\s*$", "", n)          # "Blue Cain (UGA)"
    if "," in n:                                             # "Dixon, Derek"
        last, first = [x.strip() for x in n.split(",", 1)]
        n = f"{first} {last}"
    n = re.sub(r"[.'’]", "", n.lower())
    n = re.sub(r"\s+(jr|sr|ii|iii|iv|v)$", "", n)
    return " ".join(n.split())


def same_player(a, b):
    na, nb = norm_player(a), norm_player(b)
    if na == nb:
        return True
    ta, tb = na.split(), nb.split()
    if len(ta) < 2 or len(tb) < 2 or ta[-1] != tb[-1]:
        return False
    return ta[0][0] == tb[0][0] and (ta[0].startswith(tb[0][:3]) or tb[0].startswith(ta[0][:3]))


def collect_rungs(ev, books):
    """All over-side rungs on an event: (player, stat, need, price, book, line_type, novig_or_None)."""
    rungs = []
    for b in ev.get("bookmakers") or []:
        if books and b["key"] not in books:
            continue
        for m in b.get("markets") or []:
            stat = STAT_KEYS.get(m["key"])
            if not stat or m.get("suspended_at") or m.get("period"):
                continue
            outs = m["outcomes"]
            for o in outs:
                if o.get("price") is None:
                    continue
                name = o["name"]
                mm = re.match(r"^(\d+)\+", name)
                if mm:
                    rungs.append((o.get("description") or "", stat, int(mm[1]), o["price"], b["key"], "ladder", None))
                elif name == "Over" and o.get("point") is not None:
                    need = math.floor(o["point"]) + 1
                    under = [u for u in outs if u["name"] == "Under" and u.get("description") == o.get("description")
                             and u.get("point") == o["point"] and u.get("price") is not None]
                    nv = None
                    if under:
                        x, y = implied(o["price"]), implied(under[0]["price"])
                        nv = x / (x + y)
                    rungs.append((o.get("description") or "", stat, need, o["price"], b["key"],
                                  m.get("line_type") or "main", nv))
    return rungs


def rung_estimate(vals, need, price, novig=None, prior_games=6.0, vig=0.06):
    """Shrink the raw hit rate toward the market: est = (hits + m*q) / (n + m)."""
    n = len(vals)
    k = sum(1 for v in vals if v >= need)
    imp = implied(price)
    q = novig if novig is not None else imp / (1 + vig)
    est = (k + prior_games * q) / (n + prior_games)
    return k, n, imp, est


def market_q(price, novig=None, vig=0.06):
    """The market's own probability for a rung: the no-vig number on a two-way line, else implied / (1 + vig)."""
    return novig if novig is not None else implied(price) / (1 + vig)


def opp_adjust(vals, ranks, tonight, opp_top=50, comp_top=100):
    """Opponent-quality rule (2.2). Against a top opponent, soft-schedule games do not count.

    Returns (games to score, mode). mode is None when the rule does not apply, "OPP-ADJ" when the hit rate
    uses only games against comparable opponents, and "OPP-CAP" when there are fewer than two such games,
    in which case the caller holds the estimate to the market's probability plus a small cap."""
    if not ranks or tonight is None or tonight > opp_top:
        return list(vals), None
    comp = [v for v, r in zip(vals, ranks) if r <= comp_top]
    if len(comp) >= 2:
        return comp, "OPP-ADJ"
    return list(vals), "OPP-CAP"


def parse_hist(h):
    """'Player:stat:v1,v2[@r1,r2[@tonight]]' -> (player, stat, vals, ranks or None, tonight or None).

    r1,r2 are the KenPom ranks of the opponents in those games (NR for a non-D-I team); tonight is the KenPom
    rank of tonight's opponent."""
    player, stat, rest = h.rsplit(":", 2)
    parts = rest.split("@")
    if len(parts) > 3:
        raise ValueError(h)
    vals = [float(v) for v in parts[0].split(",") if v.strip() != ""]
    rk = lambda x: 999 if x.strip().upper() == "NR" else int(x)
    ranks = [rk(x) for x in parts[1].split(",") if x.strip() != ""] if len(parts) > 1 else None
    tonight = rk(parts[2]) if len(parts) > 2 and parts[2].strip() else None
    if ranks is not None and len(ranks) != len(vals):
        raise ValueError(f"{h}: {len(vals)} games but {len(ranks)} opponent ranks")
    return player.strip(), stat.strip().lower(), vals, ranks, tonight


def cmd_ladder(a):
    ev = load_json(a.odds)
    if isinstance(ev, list):
        ev = ev[0]
    books = [b.strip() for b in a.books.split(",") if b.strip()]
    rungs = collect_rungs(ev, books)
    hist, opp = {}, {}
    for h in a.hist or []:
        try:
            player, stat, vals, ranks, tonight = parse_hist(h)
            hist[(player, stat)] = vals
            opp[(player, stat)] = (ranks, tonight)
        except ValueError as e:
            sys.exit("ERROR: --hist must look like 'James Scott:rebounds:6,7,7' or, with opponent KenPom ranks "
                     f"and tonight's opponent rank, 'James Scott:rebounds:6,7,7@210,45,12@8' (got {h!r}: {e})")
    print(f"Overs-only ladder  |  {ev.get('away_team')} @ {ev.get('home_team')}  |  books: {','.join(books)}  "
          f"|  rungs found: {len(rungs)}")
    if not rungs:
        print("No over-side player rungs at these books. Check the markets list or try another book.")
        return
    if not hist:
        print(f"{'Player':24} {'Stat':9} {'Need':>4} {'Price':>6} {'Impl':>6}  Book")
        for p, s, n, pr, b, lt, nv in sorted(rungs, key=lambda r: (norm_player(r[0]), r[1], r[2])):
            if a.min_price <= pr <= a.max_price:
                print(f"{p[:24]:24} {s:9} {n:>3}+ {fmt_am(pr):>6} {pct(implied(pr)):>6}  {b}")
        print("\nPass --hist 'Player:stat:v1,v2,...' (one per player and stat, oldest to newest) to score rungs.")
        return
    used = set()
    print(f"{'Player':22} {'Stat':9} {'Need':>4} {'Price':>6} {'Impl':>6} {'Hit':>5} {'Est':>6} {'Edge':>6}  Flags")
    for (hp, hs), vals in hist.items():
        mine = [r for r in rungs if r[1] == hs and same_player(r[0], hp)]
        if not mine:
            print(f"{hp[:22]:22} {hs:9}  UNMATCHED: no {hs} rungs for this player at {','.join(books)}")
            continue
        used.add((hp, hs))
        best = {}
        for r in mine:                       # best price per rung across books
            if r[2] not in best or dec(r[3]) > dec(best[r[2]][3]):
                best[r[2]] = r
        pick, scored = None, []
        ranks, tonight = opp.get((hp, hs), (None, None))
        vals, mode = opp_adjust(vals, ranks, tonight, a.opp_top, a.comp_top)
        for need in sorted(best):
            p, s, n_, pr, b, lt, nv = best[need]
            k, n, imp, est = rung_estimate(vals, need, pr, nv, a.prior_games, a.vig)
            flags = []
            if mode == "OPP-CAP":
                est = min(est, market_q(pr, nv, a.vig) + a.opp_cap)
            if mode:
                flags.append(mode)
            if pr < -400:
                flags.append("CHALK")
            if n < 5:
                flags.append("THIN")
            if sum(1 for v in vals if v == need) * 2 >= n and k:
                flags.append("NO-CUSHION")
            ok_rate = (k == n) if n <= 3 else (k / n >= 2 / 3)
            ok = ok_rate and pr >= -400 and est >= a.min_est and est - imp >= -0.02 and "NO-CUSHION" not in flags
            scored.append((need, pr, imp, k, n, est, flags, b, ok))
            if ok:
                pick = need
        for need, pr, imp, k, n, est, flags, b, ok in scored:
            if not (a.min_price <= pr <= a.max_price) and need != pick:
                continue
            mark = ["PICK"] if need == pick else []
            print(f"{hp[:22]:22} {hs:9} {need:>3}+ {fmt_am(pr):>6} {pct(imp):>6} {f'{k}/{n}':>5} "
                  f"{pct(est):>6} {100 * (est - imp):>+5.1f}  {','.join(mark + flags)}  [{b}]")
        if pick is None:
            print(f"{hp[:22]:22} {hs:9}  no rung passes (needs hit rate, price no worse than -400, "
                  f"est >= {a.min_est:.0%}, cushion)")
    print("\nHit = games at or above the rung. Est = hit rate shrunk toward the market price "
          f"(prior worth {a.prior_games:g} games). Edge = Est minus the price's implied probability. "
          "PICK = highest rung that passes every test. THIN = under 5 games: cap at moderate confidence. "
          f"OPP-ADJ = tonight's opponent is KenPom top {a.opp_top}, so only games against top-{a.comp_top} "
          f"opponents are counted. OPP-CAP = fewer than two such games, so Est is held to the market's "
          f"probability plus {100 * a.opp_cap:g} points.")


# ------------------------------------------------------- cover / parlay cmds


def cmd_cover(a):
    p = a.winprob / 100 if a.winprob > 1 else a.winprob
    cp, sd = cover_prob(a.margin, p, a.spread)
    blend = a.kp_weight * cp + (1 - a.kp_weight) * 0.5
    print(f"KenPom margin {a.margin:+g}, win {pct(p, 0)}, spread {a.spread:+g}  ->  SD {sd:.1f} pts")
    print(f"Cover probability: KenPom-only {pct(cp)}   blended with a 50% market {pct(blend)} "
          f"(KenPom weight {a.kp_weight})")


def price_parlay(legs, book=None, boost=0.0, stake=10.0, bonus=False):
    """legs: list of (american, est_prob_or_None, label). Returns a dict of numbers."""
    d_ind = math.prod(dec(o) for o, _, _ in legs)
    probs = [p for _, p, _ in legs]
    cash = math.prod(probs) if all(p is not None for p in probs) else None
    d_use = dec(book) if book is not None else d_ind
    profit = stake * (d_use - 1) * (1 + boost)
    out = dict(independent_decimal=d_ind, independent_american=american(d_ind),
               priced_at=american(d_use), book_tax=None if book is None else 1 - d_use / d_ind,
               profit=profit, payout=profit if bonus else profit + stake, cash_prob=cash,
               breakeven=None if bonus else stake / (stake + profit))
    if cash is not None:
        out["ev"] = cash * profit if bonus else cash * profit - (1 - cash) * stake
        out["ev_pct"] = out["ev"] / stake
    return out


def cmd_parlay(a):
    legs = []
    for s in a.leg:
        parts = s.split(":", 2)
        o = parse_american(parts[0])
        p = None
        if len(parts) > 1 and parts[1].strip():
            p = float(parts[1])
            p = p / 100 if p > 1 else p
        legs.append((o, p, parts[2].strip() if len(parts) > 2 else ""))
    book = parse_american(a.book) if a.book else None
    r = price_parlay(legs, book, a.boost / 100, a.stake, a.bonus)
    print(f"{'Leg':40} {'Price':>6} {'Impl':>6} {'Est':>6}")
    for o, p, lab in legs:
        print(f"{(lab or '-')[:40]:40} {fmt_am(o):>6} {pct(implied(o)):>6} {pct(p):>6}")
    print(f"\nIndependent price: {fmt_am(r['independent_american'])} (decimal {r['independent_decimal']:.3f})")
    if book is not None:
        tax = r["book_tax"]
        word = "book tax" if tax >= 0 else "book is paying MORE than independent math"
        print(f"Book price: {fmt_am(book)}  ->  {word} {abs(tax):.1%}")
    kind = "bonus bet (stake not returned)" if a.bonus else "cash"
    bo = f", {a.boost:g}% profit boost" if a.boost else ""
    print(f"${a.stake:g} {kind}{bo}: profit ${r['profit']:.2f}, total back ${r['payout']:.2f}")
    if r["breakeven"] is not None:
        print(f"Break-even chance to cash: {pct(r['breakeven'])}")
    if r["cash_prob"] is not None:
        print(f"Chance to cash (legs treated as independent): {pct(r['cash_prob'])}")
        print("  Same-game legs that help each other cash together more often than this; "
              "legs that fight each other cash less often.")
        print(f"EV: ${r['ev']:+.2f} ({r['ev_pct']:+.1%} of stake)")
    else:
        print("Add an estimate to every leg ('-115:0.60:label') to get chance to cash and EV.")
    if a.min_odds is not None:
        ok = dec(parse_american(a.min_odds)) <= dec(r["priced_at"])
        print(f"Boost minimum {a.min_odds}: {'QUALIFIES' if ok else 'DOES NOT QUALIFY'} at {fmt_am(r['priced_at'])}")


# ------------------------------------------------------------------- ledger

LEDGER_COLS = ["ticket_id", "date", "book", "ticket_type", "stake", "ticket_odds", "boost_pct", "bonus_bet",
               "ticket_result", "payout", "profit", "leg_no", "event_id", "game", "market", "selection",
               "line", "leg_odds", "est_prob", "tier", "kp_edge", "closing_odds", "leg_result", "notes", "label"]
LABELS = ("edge", "fair", "override", "bonus", "")
MARKETS = ("ml", "spread", "total", "points", "rebounds", "assists", "threes", "combo", "other")


def read_ledger(path):
    if not os.path.exists(path):
        return []
    with open(path, newline="", encoding="utf-8") as f:
        return [r for r in csv.DictReader(f) if (r.get("ticket_id") or "").strip()]


def write_ledger(path, rows):
    def _w(p):
        with open(p, "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=LEDGER_COLS, extrasaction="ignore")
            w.writeheader()
            w.writerows(rows)
    try:
        _w(path)
        return path
    except (PermissionError, OSError):
        alt = os.path.join(os.getcwd(), os.path.basename(path))
        _w(alt)
        return alt


def cmd_log(a):
    rows = read_ledger(a.ledger)
    t = json.loads(a.ticket)
    ttype = t.get("type", "sgp").lower()
    if ttype not in ("single", "parlay", "sgp"):
        sys.exit("ERROR: type must be single, parlay or sgp")
    legs = t.get("legs") or []
    if not legs or (ttype == "single") != (len(legs) == 1):
        sys.exit("ERROR: a single has exactly one leg; a parlay or sgp has two or more")
    for l in legs:
        if l.get("market") not in MARKETS:
            sys.exit(f"ERROR: leg market must be one of {MARKETS} (got {l.get('market')!r})")
        parse_american(l["odds"])
    sig = lambda date, book, ls: (str(date), str(book), tuple(sorted((str(x[0]), fmt_am(parse_american(x[1]))) for x in ls)))
    new_sig = sig(t["date"], t.get("book", ""), [(l["selection"], l["odds"]) for l in legs])
    by_id = {}
    for r in rows:
        by_id.setdefault(r["ticket_id"], []).append(r)
    for k, v in by_id.items():
        if sig(v[0]["date"], v[0]["book"], [(r["selection"], r["leg_odds"]) for r in v]) == new_sig and not a.force:
            sys.exit(f"ERROR: this ticket is already logged as #{k}. Pass --force to log it again.")
    label = str(t.get("label", "")).lower()
    if label not in LABELS:
        sys.exit(f"ERROR: label must be one of edge, fair, override, bonus (got {label!r})")
    ids = [int(r["ticket_id"]) for r in rows if r["ticket_id"].isdigit()]
    base = 1001 if ttype == "sgp" else 1
    same = [i for i in ids if (i >= 1001) == (ttype == "sgp")]
    tid = max(same) + 1 if same else base
    if ttype != "sgp" and tid >= 1001:
        sys.exit("ERROR: single/parlay ids have reached 1000; renumber before logging")
    d_ind = math.prod(dec(parse_american(l["odds"])) for l in legs)
    odds = parse_american(t["odds"]) if t.get("odds") not in (None, "") else american(d_ind)
    for i, l in enumerate(legs, 1):
        rows.append(dict(
            ticket_id=tid, date=t["date"], book=t.get("book", ""), ticket_type=ttype, stake=t["stake"],
            ticket_odds=fmt_am(odds), boost_pct=t.get("boost", 0), bonus_bet="Y" if t.get("bonus") else "N",
            ticket_result="pending", payout="", profit="", leg_no=i, event_id=l.get("event_id", ""),
            game=l.get("game", ""), market=l["market"], selection=l["selection"], line=l.get("line", ""),
            leg_odds=fmt_am(parse_american(l["odds"])), est_prob=l.get("est", ""), tier=l.get("tier", ""),
            kp_edge=l.get("kp_edge", ""), closing_odds="", leg_result="pending", notes=l.get("notes", ""),
            label=label))
    out = write_ledger(a.ledger, rows)
    if not label:
        print("NOTE: no label given. Add \"label\": \"edge\", \"fair\" or \"override\" so the audit can separate them.")
    print(f"Logged ticket #{tid} ({ttype}{', ' + label if label else ''}, {len(legs)} leg{'s' if len(legs) > 1 else ''}, "
          f"${t['stake']} at {fmt_am(odds)}) -> {out}")


def cmd_settle(a):
    rows = read_ledger(a.ledger)
    mine = [r for r in rows if r["ticket_id"] == str(a.id)]
    if not mine:
        sys.exit(f"ERROR: ticket #{a.id} not in {a.ledger}")
    res = [x.strip().upper() for x in a.legs.split(",")]
    if len(res) != len(mine) or any(x not in ("W", "L", "P", "V") for x in res):
        sys.exit(f"ERROR: give one of W/L/P/V per leg, {len(mine)} legs on this ticket")
    closing = [x.strip() for x in a.closing.split(",")] if a.closing else [""] * len(mine)
    if len(closing) != len(mine):
        sys.exit("ERROR: --closing needs one price per leg (blank allowed)")
    stake = float(mine[0]["stake"])
    bonus = mine[0]["bonus_bet"] == "Y"
    boost = float(mine[0]["boost_pct"] or 0) / 100
    live = [(r, x) for r, x in zip(mine, res) if x == "W"]
    if "L" in res:
        result, profit = "L", (0.0 if bonus else -stake)
    elif not live:
        result, profit = "P", 0.0
    else:
        if all(x == "W" for x in res):
            d = dec(parse_american(mine[0]["ticket_odds"]))
        else:                                   # pushed/voided legs drop out; reprice from leg odds
            d = math.prod(dec(parse_american(r["leg_odds"])) for r, _ in live)
        result, profit = "W", stake * (d - 1) * (1 + boost)
    if a.payout is not None:                   # cashout or a book-specific payout overrides
        profit = a.payout - (0 if bonus else stake)
        result = "CASHOUT" if a.cashout else result
    payout = profit + (0 if bonus else stake) if result != "L" else 0.0
    if a.label is not None:
        if a.label.lower() not in LABELS:
            sys.exit("ERROR: --label must be edge, fair, override or bonus")
        for r in mine:
            r["label"] = a.label.lower()
    for r, x, c in zip(mine, res, closing):
        r.update(leg_result=x, ticket_result=result, payout=f"{payout:.2f}", profit=f"{profit:.2f}")
        if c:
            r["closing_odds"] = fmt_am(parse_american(c))
    out = write_ledger(a.ledger, rows)
    print(f"Ticket #{a.id}: {result}, profit ${profit:+.2f}, legs {''.join(res)} -> {out}")


def cmd_audit(a):
    rows = read_ledger(a.ledger)
    if not rows:
        print("Ledger is empty. No record yet - use the carried-over 2026 priors in the instructions.")
        return
    tickets = {}
    for r in rows:
        tickets.setdefault(r["ticket_id"], []).append(r)
    done = {k: v for k, v in tickets.items() if v[0]["ticket_result"] not in ("pending", "")}
    pend = [k for k in tickets if k not in done]
    staked = sum(float(v[0]["stake"]) for v in done.values() if v[0]["bonus_bet"] != "Y")
    profit = sum(float(v[0]["profit"] or 0) for v in done.values())
    wins = sum(1 for v in done.values() if v[0]["ticket_result"] in ("W", "CASHOUT") and float(v[0]["profit"] or 0) > 0)
    print(f"LEDGER AUDIT  |  tickets settled: {len(done)}  pending: {len(pend)}")
    if done:
        roi = f"{profit / staked:+.1%}" if staked else "n/a (bonus bets only)"
        print(f"Tickets cashed: {wins}/{len(done)} ({wins / len(done):.0%})   cash staked ${staked:.2f}   "
              f"profit ${profit:+.2f}   ROI {roi}")
        print("\nBy ticket type:")
        for tt in ("single", "parlay", "sgp"):
            v = [x for x in done.values() if x[0]["ticket_type"] == tt]
            if v:
                w = sum(1 for x in v if float(x[0]["profit"] or 0) > 0)
                pr = sum(float(x[0]["profit"] or 0) for x in v)
                print(f"  {tt:7} {w}/{len(v)} cashed   profit ${pr:+.2f}")
        labs = sorted({(x[0].get("label") or "unlabeled") for x in done.values()})
        if labs != ["unlabeled"]:
            print("\nBy label (EDGE and FAIR are the copilot's slips; OVERRIDE are slips Dustin asked for against a rule):")
            for lb in labs:
                v = [x for x in done.values() if (x[0].get("label") or "unlabeled") == lb]
                w = sum(1 for x in v if float(x[0]["profit"] or 0) > 0)
                pr = sum(float(x[0]["profit"] or 0) for x in v)
                print(f"  {lb:9} {w}/{len(v)} cashed   profit ${pr:+.2f}")
    legs = [r for r in rows if r["leg_result"] in ("W", "L")]
    if legs:
        print(f"\nLegs by market (W-L, hit rate vs the average break-even price and the average estimate):")
        print(f"  {'Market':9} {'W-L':>7} {'Hit':>6} {'B/E':>6} {'Est':>6}  Verdict")
        for mk in MARKETS:
            v = [r for r in legs if r["market"] == mk]
            if not v:
                continue
            w = sum(1 for r in v if r["leg_result"] == "W")
            hit = w / len(v)
            be = statistics.mean(implied(parse_american(r["leg_odds"])) for r in v)
            ests = [float(r["est_prob"]) for r in v if r["est_prob"] not in ("", None)]
            est = statistics.mean(ests) if ests else None
            verdict = "small sample" if len(v) < a.min_sample else (
                "LEAK - restrict" if hit < be - 0.05 else "EDGE - lean in" if hit > be + 0.05 else "in line")
            print(f"  {mk:9} {f'{w}-{len(v) - w}':>7} {pct(hit, 0):>6} {pct(be, 0):>6} {pct(est, 0):>6}  {verdict}")
        tiers = sorted({r["tier"] for r in legs if r["tier"]})
        if tiers:
            print("\nCalibration by confidence tier (does the tier hit as often as estimated?):")
            for t in tiers:
                v = [r for r in legs if r["tier"] == t]
                w = sum(1 for r in v if r["leg_result"] == "W")
                ests = [float(r["est_prob"]) for r in v if r["est_prob"] not in ("", None)]
                print(f"  {t:10} {w}-{len(v) - w}  hit {pct(w / len(v), 0)}  "
                      f"estimated {pct(statistics.mean(ests), 0) if ests else 'n/a'}")
        clv = []
        for r in legs:
            if r.get("closing_odds"):
                try:
                    clv.append(dec(parse_american(r["leg_odds"])) / dec(parse_american(r["closing_odds"])) - 1)
                except ValueError:
                    pass
        if clv:
            beat = sum(1 for c in clv if c > 0)
            print(f"\nClosing-line value (price taken vs closing price): average {statistics.mean(clv):+.1%}, "
                  f"beat the close on {beat}/{len(clv)} legs")
    if pend:
        print("\nPending tickets: " + ", ".join(f"#{k}" for k in sorted(pend, key=int)))


# ----------------------------------------------------------------- selftest


def cmd_selftest(_):
    ok = True

    def check(name, cond):
        nonlocal ok
        ok &= bool(cond)
        print(("PASS  " if cond else "FAIL  ") + name)

    check("implied(-115) = 53.5%", abs(implied(-115) - 0.5349) < 1e-3)
    check("dec(+150) = 2.5", abs(dec(150) - 2.5) < 1e-9)
    check("american(3.658) = +266", american(dec(-115) * dec(-230) * dec(-275)) == 266)
    cp, sd = cover_prob(7, 0.73, -3.5)
    check("cover(7, 73%, -3.5) = 62%, SD 11.4", abs(cp - 0.62) < 0.005 and abs(sd - 11.4) < 0.1)
    fm = ("12 Arizona at\n21 Auburn\tAuburn 80-78 (55%) [72]\t9:00 PM\n ESPN2 \n"
          "56 Mississippi St. vs.\n39 Xavier\tXavier 82-79 (61%) [75]\t9:00 PM\n"
          "63 Pittsburgh at\n88 Butler\tPittsburgh 79-78 (51%) [73]\t6:30 PM\n"
          "NR Mary Baldwin at\n302 VMI\t\t7:00 PM\n"
          "314 Cleveland St. 69,\n349 West Florida 67 [66]\nMVP: X\n\tCleveland St. 81-78 (62%) [71]\tbox\n"
          "66 Georgia at 45 North Carolina North Carolina 83-76 (73%) [72] 7:00 PM\n")
    g, bad = parse_fanmatch(fm)
    check("FanMatch: 4 games parsed, none unparsed", len(g) == 4 and not bad)
    check("FanMatch: away winner + neutral site read", g[2]["winner"] == "Pittsburgh" and g[1]["neutral"])
    check("FanMatch: single-line row read", g[3]["home"] == "North Carolina" and g[3]["sw"] - g[3]["sl"] == 7)
    check("names: UConn = Connecticut", team_sim("Connecticut", "UConn") == 1.0)
    check("names: N.C. State = NC State", team_sim("N.C. State", "NC State") == 1.0)
    check("names: mascot stripped", team_sim("Bryant", "Bryant Bulldogs") >= 0.85)
    check("names: North Carolina != North Carolina Central",
          team_sim("North Carolina", "North Carolina Central") < 0.8)
    ev = dict(id="1", home_team="Gonzaga", away_team="LSU", live=False, bookmakers=[
        dict(key="polymarket", markets=[dict(key="h2h", line_type="main", outcomes=[
            dict(name="Gonzaga Bulldogs", price=-223, side="home"), dict(name="LSU Tigers", price=212, side="away")])]),
        dict(key="fanduel", markets=[dict(key="h2h", line_type="main", outcomes=[
            dict(name="Gonzaga", price=-220, side="home"), dict(name="LSU", price=180, side="away")]),
            dict(key="spreads", line_type="main", outcomes=[
            dict(name="Gonzaga Bulldogs", price=-110, point=-5.5), dict(name="LSU Tigers", price=-110, point=5.5)])])])
    rows, un = build_board([dict(away="LSU", home="Gonzaga", winner="Gonzaga", sw=82, sl=75, p=0.73, neutral=False,
                                 tempo=70)], [ev])
    check("board: prices read by side when a book adds the mascot",
          not un and rows[0]["ml_books"] == 2 and rows[0]["best_ml"] == (-220, "fanduel") and rows[0]["mk_spread"] == -5.5)
    check("work: KenPom can lift the market by 2 points at most", abs(working_prob(0.73, 0.61, 0.35) - 0.63) < 1e-9
          and abs(working_prob(0.50, 0.70, 0.5) - 0.67) < 1e-9)
    ev2 = dict(id="2", home_team="Oakland", away_team="Northern Iowa", live=False, commence_time="2026-11-14T22:00:00Z",
               bookmakers=[dict(key="fanduel", markets=[dict(key="h2h", line_type="main", outcomes=[
                   dict(name="Oakland", price=-120, side="home"), dict(name="Northern Iowa", price=100, side="away")])])])
    g2 = dict(away="Northern Iowa", home="Oakland", winner="Northern Iowa", sw=74, sl=72, p=0.58, neutral=False, tempo=68)
    rows2, _ = build_board([g2], [ev2], kp_weight=0.35, played_yesterday={norm_team("Northern Iowa")})
    check("board: KenPom pick that the market has as the underdog is flagged, with rest",
          rows2[0]["play"] == "Northern Iowa" and rows2[0]["work_p"] < 0.5 and "KP-VS-MKT" in rows2[0]["flags"]
          and "B2B" in rows2[0]["flags"])
    ev3 = dict(id="3", home_team="Siena", away_team="Brown", live=False, bookmakers=[dict(key="fanduel", markets=[
        dict(key="h2h", line_type="main", outcomes=[dict(name="Siena", price=-250, side="home"),
                                                    dict(name="Brown", price=200, side="away")])])])
    rows4, _ = build_board([dict(away="Brown", home="Siena", winner="Brown", sw=70, sl=69, p=0.51, neutral=False,
                                 tempo=66)], [ev3], kp_weight=0.35)
    check("board: plays the market favorite when KenPom barely leans the other way",
          rows4[0]["play"] == "Siena" and abs(rows4[0]["work_p"] - (rows4[0]["mk_p"] - 0.03)) < 1e-9
          and "KP-VS-MKT" in rows4[0]["flags"])
    ev["commence_time"] = "2026-11-14T20:30:00Z"
    rows3, _ = build_board([dict(away="LSU", home="Gonzaga", winner="Gonzaga", sw=82, sl=75, p=0.73, neutral=False,
                                 tempo=70), g2], [ev, ev2], kp_weight=0.35)
    rows3 = json.loads(json.dumps(rows3, default=str))
    sl = find_slips(rows3, ["fanduel"], 2, 3, 0.45, None, 0.0, 5.0, False, 3, False)
    check("build: finds the two-leg FanDuel slip and prices it", len(sl) == 1 and len(sl[0]["legs"]) == 2
          and abs(sl[0]["dec"] - dec(-220) * dec(100)) < 1e-9)
    check("build: 60% bar keeps the coin flip out", not find_slips(rows3, ["fanduel"], 2, 3, 0.60, None, 0.0, 5.0,
                                                                   False, 3, False))
    check("time: 20:30 UTC in November is 3:30 PM Eastern", et_time("2026-11-14T20:30:00Z") == (930, "3:30 PM"))
    check("players: 'Dixon, Derek' = 'Derek Dixon'", same_player("Dixon, Derek", "Derek Dixon"))
    check("players: Neo = Neoklis Avdalas (UNC)", same_player("Neo Avdalas", "Neoklis Avdalas (UNC)"))
    k, n, imp, est = rung_estimate([6, 7, 7], 6, -230)
    check("ladder: 3/3 at -230 shrinks to ~77%", k == 3 and abs(est - 0.772) < 0.01)
    check("opp rule: one comparable game vs a top-50 opponent -> OPP-CAP on all games",
          opp_adjust([16, 12, 6, 12], [332, 232, 5, 298], 6) == ([16, 12, 6, 12], "OPP-CAP"))
    check("opp rule: two comparable games -> OPP-ADJ on those games only",
          opp_adjust([10, 20, 15], [40, 80, 300], 12) == ([10, 20], "OPP-ADJ"))
    check("opp rule: opponent outside the top 50, or no ranks given -> unchanged",
          opp_adjust([10, 20, 15], [40, 80, 300], 120)[1] is None and opp_adjust([10, 20], None, None)[1] is None)
    check("opp rule: hist with ranks parses", parse_hist("Dame Sarr:points:16,12,6,12@332,NR,5,298@6")
          == ("Dame Sarr", "points", [16.0, 12.0, 6.0, 12.0], [332, 999, 5, 298], 6))
    kk, nn, ii, ee = rung_estimate([16, 12, 6, 12], 11, -118, 0.517)
    check("opp rule: capped estimate is market + 2 pts (51.7% -> 53.7%)",
          abs(min(ee, market_q(-118, 0.517) + 0.02) - 0.537) < 1e-9 and ee > 0.60)
    r = price_parlay([(-115, .6, ""), (-230, .7, ""), (-275, .7, "")], book=230, boost=0.3, stake=5)
    check("parlay: tax 9.8%, boosted profit $14.95", abs(r["book_tax"] - 0.098) < 0.002 and abs(r["profit"] - 14.95) < 0.01)
    print("\nALL CHECKS PASSED" if ok else "\nSOME CHECKS FAILED")
    sys.exit(0 if ok else 1)


# --------------------------------------------------------------------- main


def main():
    ap = argparse.ArgumentParser(description=f"NCAAB Copilot engine {VERSION}")
    sub = ap.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("slate", help="edge board: KenPom FanMatch vs PropLine market")
    s.add_argument("--fanmatch", required=True, help="text of kenpom.com/fanmatch.php saved to a file")
    s.add_argument("--odds", required=True, help="saved propline_get_odds result for basketball_ncaab")
    s.add_argument("--books", default=BETTABLE)
    s.add_argument("--kp-weight", type=float, default=0.5, help="KenPom share of the blended probability")
    s.add_argument("--min-edge", type=float, default=None, help="only show games with at least this edge (pts)")
    s.add_argument("--min-work", type=float, default=None, help="only show plays at or above this working probability (percent)")
    s.add_argument("--prev-fanmatch", help="yesterday's FanMatch text, to flag teams on a second game in two days")
    s.add_argument("--alias", action="append", help="'KenPom name=PropLine name' (repeatable)")
    s.add_argument("--json", help="also save the board as JSON")
    s.add_argument("--include-live", action="store_true", help="also list games already in progress")
    s.set_defaults(fn=cmd_slate)

    bd = sub.add_parser("build", help="best slips from a saved edge board, labeled EDGE / FAIR / OVERRIDE")
    bd.add_argument("--board", required=True, help="JSON saved by: slate --json board.json")
    bd.add_argument("--books", default=BETTABLE, help="books to build at; a book PropLine lacks uses reference prices")
    bd.add_argument("--min-legs", type=int, default=2)
    bd.add_argument("--max-legs", type=int, default=None, help="default 3, or 4 for a boost or bonus bet with a minimum")
    bd.add_argument("--min-prob", type=float, default=None,
                    help="bar for every leg: default 0.60, or 0.55 for a boost or bonus bet with a minimum")
    bd.add_argument("--min-odds", help="promo minimum before the boost, e.g. +400")
    bd.add_argument("--worst-leg", type=float, default=-400, help="shortest price allowed on a leg (default -400)")
    bd.add_argument("--boost", type=float, default=0.0, help="profit boost percent")
    bd.add_argument("--stake", type=float, default=5.0)
    bd.add_argument("--bonus", action="store_true", help="bonus bet: stake not returned")
    bd.add_argument("--tip-from", help="earliest tip, Eastern, 24h HH:MM")
    bd.add_argument("--tip-to", help="latest tip, Eastern, 24h HH:MM")
    bd.add_argument("--exclude", help="comma-separated team names to leave out (unexplained line move, injury doubt)")
    bd.add_argument("--top", type=int, default=3, help="how many slips to return")
    bd.add_argument("--allow-overlap", action="store_true", help="let slips share a game")
    bd.add_argument("--override-only", action="store_true", help="show only the rule-breaking option")
    bd.set_defaults(fn=cmd_build)

    l = sub.add_parser("ladder", help="overs-only alt-line board for one game")
    l.add_argument("--odds", required=True, help="saved propline_get_odds result for ONE event (player markets)")
    l.add_argument("--books", default="draftkings")
    l.add_argument("--hist", action="append",
                   help="'Player:stat:v1,v2,...' oldest to newest (repeatable). Add '@r1,r2,...' for the KenPom rank of "
                        "each game's opponent and '@N' for tonight's opponent rank, e.g. 'Dame Sarr:points:16,12,6,12@332,232,5,298@6'")
    l.add_argument("--opp-top", type=int, default=50, help="opponent-quality rule applies when tonight's opponent is ranked this or better")
    l.add_argument("--comp-top", type=int, default=100, help="games against opponents ranked this or better count as comparable")
    l.add_argument("--opp-cap", type=float, default=0.02, help="with fewer than two comparable games, Est is capped at market + this")
    l.add_argument("--prior-games", type=float, default=6.0)
    l.add_argument("--vig", type=float, default=0.06)
    l.add_argument("--min-est", type=float, default=0.60)
    l.add_argument("--min-price", type=float, default=-600)
    l.add_argument("--max-price", type=float, default=250)
    l.set_defaults(fn=cmd_ladder)

    c = sub.add_parser("cover", help="cover probability from KenPom margin and win probability")
    c.add_argument("--margin", type=float, required=True)
    c.add_argument("--winprob", type=float, required=True)
    c.add_argument("--spread", type=float, required=True, help="as quoted for KenPom's winner, e.g. -3.5")
    c.add_argument("--kp-weight", type=float, default=0.5)
    c.set_defaults(fn=cmd_cover)

    p = sub.add_parser("parlay", help="price a slip: tax, boost, bonus bet, chance to cash, EV")
    p.add_argument("--leg", action="append", required=True, help="'odds[:est[:label]]', e.g. '-115:0.60:UNC -3.5'")
    p.add_argument("--book", help="the book's actual parlay/SGP price")
    p.add_argument("--boost", type=float, default=0.0, help="profit boost percent")
    p.add_argument("--stake", type=float, default=10.0)
    p.add_argument("--bonus", action="store_true", help="bonus bet: stake not returned")
    p.add_argument("--min-odds", help="boost's minimum odds, e.g. +300")
    p.set_defaults(fn=cmd_parlay)

    g = sub.add_parser("log", help="append a placed ticket to the ledger")
    g.add_argument("--ledger", required=True)
    g.add_argument("--ticket", required=True, help="JSON: date, book, type, stake, odds, boost, bonus, legs[]")
    g.add_argument("--force", action="store_true", help="log even if an identical ticket exists")
    g.set_defaults(fn=cmd_log)

    t = sub.add_parser("settle", help="record a ticket's results")
    t.add_argument("--ledger", required=True)
    t.add_argument("--id", required=True, type=int)
    t.add_argument("--legs", required=True, help="W/L/P/V per leg, comma-separated")
    t.add_argument("--closing", help="closing price per leg, comma-separated (blank allowed)")
    t.add_argument("--payout", type=float, help="actual amount returned (cashout or book rounding)")
    t.add_argument("--cashout", action="store_true")
    t.add_argument("--label", help="set or correct the ticket's label: edge, fair, override or bonus")
    t.set_defaults(fn=cmd_settle)

    u = sub.add_parser("audit", help="record, ROI, calibration, CLV and leaks from the ledger")
    u.add_argument("--ledger", required=True)
    u.add_argument("--min-sample", type=int, default=10)
    u.set_defaults(fn=cmd_audit)

    sub.add_parser("selftest", help="run built-in checks").set_defaults(fn=cmd_selftest)

    # A value such as "-155:0.61:NKU" starts with a dash, and argparse would read it as an option.
    # Join each of these flags to its value so any odds or line is accepted as written.
    joined = {"--leg", "--book", "--min-odds", "--closing", "--legs", "--spread", "--hist", "--alias", "--ticket",
              "--exclude", "--worst-leg"}
    argv, raw, i = [], sys.argv[1:], 0
    while i < len(raw):
        if raw[i] in joined and i + 1 < len(raw):
            argv.append(raw[i] + "=" + raw[i + 1])
            i += 2
        else:
            argv.append(raw[i])
            i += 1
    a = ap.parse_args(argv)
    a.fn(a)


if __name__ == "__main__":
    main()
