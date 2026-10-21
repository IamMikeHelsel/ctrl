#!/usr/bin/env bash
# Watch bounty sources for entries that newly become claimable, and diff against stored snapshots.
#
#   JSP catalog        TheJustinSunPrize/awards problems/catalog-*.md (+ mathdb-pilot.json)
#   erdosproblems.com  teorth/erdosproblems data/problems.yaml
#   formal-conjectures google-deepmind/formal-conjectures FormalConjectures/ErdosProblems/*.lean
#
# Usage: scripts/bounty_watch.sh [-q] [--jsp-from FILE]
#   -q              print nothing when there are no changes and no failures (for cron)
#   --jsp-from FILE parse a local concatenated JSP catalog instead of fetching it
# Env:   SNAPSHOT_DIR (default <repo>/data/snapshots)
# Exit:  0 ok (with or without changes), 2 at least one source failed (its snapshot is kept).
# The first run for a source records a baseline and reports nothing for it.
set -euo pipefail
export PATH="/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:${PATH:-}"
export LC_ALL="${LC_ALL:-en_US.UTF-8}"

QUIET=0
JSP_FROM=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    -q) QUIET=1 ;;
    --jsp-from) JSP_FROM="$2"; shift ;;
    -h|--help) sed -n '2,15p' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 64 ;;
  esac
  shift
done

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SNAP="${SNAPSHOT_DIR:-$REPO/data/snapshots}"
mkdir -p "$SNAP"

LOCK="$SNAP/.lock"
if [[ -d "$LOCK" ]] && [[ -n "$(find "$LOCK" -maxdepth 0 -mmin +120 2>/dev/null)" ]]; then
  rmdir "$LOCK" 2>/dev/null || true
fi
if ! mkdir "$LOCK" 2>/dev/null; then
  echo "bounty_watch: another run holds $LOCK" >&2
  exit 0
fi
WORK="$(mktemp -d "${TMPDIR:-/tmp}/bounty_watch.XXXXXX")"
trap 'rm -rf "$WORK"; rmdir "$LOCK" 2>/dev/null || true' EXIT

fetch() { curl -sSfL --retry 3 --retry-delay 5 --max-time 180 -A bounty_watch -o "$2" "$1"; }

JSP_RAW="https://raw.githubusercontent.com/TheJustinSunPrize/awards/main/problems"
FAILED=()

mkdir -p "$WORK/jsp"
if [[ -n "$JSP_FROM" ]]; then
  cp "$JSP_FROM" "$WORK/jsp/catalog-local.md" 2>>"$WORK/err" \
    || { FAILED+=("jsp: cannot read $JSP_FROM"); rm -rf "$WORK/jsp"; }
else
  vols=""
  if fetch "$JSP_RAW/README.md" "$WORK/jsp_readme.md" 2>"$WORK/err"; then
    vols="$(grep -oE 'catalog-[0-9]+-[0-9]+\.md' "$WORK/jsp_readme.md" | sort -u || true)"
  fi
  if [[ -z "$vols" ]] && command -v jq >/dev/null; then
    vols="$(curl -sSfL --max-time 60 https://api.github.com/repos/TheJustinSunPrize/awards/contents/problems \
      | jq -r '.[].name | select(test("^catalog-[0-9]+-[0-9]+\\.md$"))' 2>/dev/null || true)"
  fi
  if [[ -z "$vols" ]]; then
    FAILED+=("jsp: could not list catalog volumes")
  else
    for v in $vols; do
      if ! fetch "$JSP_RAW/$v" "$WORK/jsp/$v" 2>>"$WORK/err"; then
        FAILED+=("jsp: fetch $v failed")
        rm -rf "$WORK/jsp"; break
      fi
    done
  fi
fi
[[ -d "$WORK/jsp" ]] && { fetch "$JSP_RAW/mathdb-pilot.json" "$WORK/jsp/mathdb-pilot.json" 2>/dev/null || true; }

fetch https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml "$WORK/erdos.yaml" 2>>"$WORK/err" \
  || FAILED+=("erdos: fetch data/problems.yaml failed")

fetch https://codeload.github.com/google-deepmind/formal-conjectures/tar.gz/refs/heads/main "$WORK/fc.tgz" 2>>"$WORK/err" \
  || FAILED+=("fc: fetch tarball failed")

FAILED_STR="$(printf '%s\n' ${FAILED[@]+"${FAILED[@]}"})"
set +e
python3 - "$WORK" "$SNAP" "$QUIET" "$FAILED_STR" <<'PY'
import json, os, re, sys, tarfile, datetime

work, snap, quiet, failed_str = sys.argv[1], sys.argv[2], sys.argv[3] == "1", sys.argv[4]
failed = [l for l in failed_str.splitlines() if l.strip()]
now = datetime.datetime.now().astimezone().isoformat(timespec="seconds")
RESOLVED = {"proved", "disproved", "solved"}

# ---------- fast-filter index loading ----------
fast_filter_plby = set()
fast_filter_prs = {}
fast_filter_erdos = {}
try:
    p_path = os.path.join(snap, "plby_erdos.json")
    if os.path.exists(p_path):
        fast_filter_plby = set(json.load(open(p_path)).get("solved_erdos", []))
    a_path = os.path.join(snap, "awards_prs.json")
    if os.path.exists(a_path):
        for pr in json.load(open(a_path)).get("prs", []):
            st = pr.get("state", "").upper()
            jids = {f"JSP-{int(j):06d}" for j in re.findall(r'JSP-(\d+)', pr.get('title',''), re.IGNORECASE) + re.findall(r'jsp-(\d+)', pr.get('head',''), re.IGNORECASE)}
            for jid in jids:
                d = fast_filter_prs.setdefault(jid, {"open": 0, "merged": 0, "plby": False})
                if st == "OPEN": d["open"] += 1
                elif st == "MERGED": d["merged"] += 1
                if "plby" in pr.get("title","").lower() or "plby" in pr.get("head","").lower():
                    d["plby"] = True
    m_path = os.path.join(snap, "jsp_erdos_map.json")
    if os.path.exists(m_path):
        fast_filter_erdos = {k: set(v) for k, v in json.load(open(m_path)).get("mappings", {}).items()}
except Exception:
    pass

def jsp_filter_reason(jid):
    reasons = []
    pr = fast_filter_prs.get(jid, {})
    if pr.get("plby"):
        reasons.append("plby PR")
    erdos_nums = fast_filter_erdos.get(jid, set())
    if any(e in fast_filter_plby for e in erdos_nums):
        reasons.append("in plby")
    if pr.get("open", 0) > 0:
        reasons.append(f"{pr['open']} open PRs")
    if pr.get("merged", 0) > 0:
        reasons.append(f"{pr['merged']} merged PRs")
    return "; ".join(reasons)

# ---------- parsers ----------
def parse_jsp(d):
    files = sorted(f for f in os.listdir(d) if f.endswith(".md"))
    if not files:
        raise ValueError("no catalog volumes")
    mathdb = {}
    mp = os.path.join(d, "mathdb-pilot.json")
    if os.path.exists(mp):
        try:
            for p in json.load(open(mp)).get("problems", []):
                mathdb[p["jsp"]] = (p.get("mathdb") or {}).get("status", "?")
        except Exception:
            pass
    text = "\n".join(open(os.path.join(d, f), encoding="utf-8").read() for f in files)
    out = {}
    parts = re.split(r"^## (JSP-\d+) · (.*)$", text, flags=re.M)
    for i in range(1, len(parts) - 2, 3):
        jid, title, body = parts[i], parts[i + 1].strip(), parts[i + 2]
        def field(name):
            m = re.search(r"^\| " + re.escape(name) + r" \| (.*?) \|\s*$", body, flags=re.M)
            return m.group(1).strip() if m else ""
        status = field("Current status")
        lean = field("Lean proof")
        elig = field("Eligible to claim")
        if elig.startswith("[See MathDB"):
            elig = "MathDB:" + mathdb.get(jid, "?")
        out[jid] = {
            "title": title,
            "status": re.split(r"<br>|\s", status, maxsplit=1)[0] if status else "",
            "lean": (re.match(r"\w+", lean) or [""])[0],
            "lean_urls": sorted(set(re.findall(r"\]\((https?://[^)\s]+)\)", lean))),
            "eligible": re.sub(r"<br>.*", "", elig).strip(),
        }
    return out, None

def parse_erdos(path):
    out, cur, nested = {}, None, None
    for line in open(path, encoding="utf-8"):
        m = re.match(r'^- number:\s*"?([^"\s]+)"?', line)
        if m:
            cur = out.setdefault(m.group(1), {}); nested = None; continue
        if cur is None:
            continue
        m = re.match(r"^  (\w+):\s*(.*?)\s*$", line)
        if m:
            k, v = m.groups()
            if v == "":
                nested = k
            else:
                nested = None
                if k == "prize":
                    cur["prize"] = v.strip('"')
            continue
        m = re.match(r'^    state:\s*"?(.*?)"?\s*$', line)
        if m and nested in ("status", "formal_status"):
            cur[nested] = m.group(1)
    return out, None

DECL = re.compile(r"@\[([^\]]*)\]\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+([^\s:({\[]+)")
def parse_fc(path):
    out = {}
    with tarfile.open(path, "r:gz") as tf:
        rev = (tf.pax_headers or {}).get("comment")
        for mem in tf:
            m = re.search(r"/FormalConjectures/ErdosProblems/([^/]+)\.lean$", mem.name)
            if not m or not mem.isfile():
                continue
            stem = m.group(1)
            src = tf.extractfile(mem).read().decode("utf-8", "replace")
            decls = list(DECL.finditer(src))
            for j, d in enumerate(decls):
                attrs, name = d.group(1), d.group(2)
                cat = re.search(r"category\s+(research\s+(?:open|solved)|\w+)", attrs)
                end = decls[j + 1].start() if j + 1 < len(decls) else len(src)
                out[f"{stem}/{name}"] = {
                    "category": re.sub(r"\s+", " ", cat.group(1)) if cat else "",
                    "sorry": bool(re.search(r"\bsorry\b", src[d.end():end])),
                    "formal_proof": sorted(re.findall(r'formal_proof\s+using\s+\w+\s+at\s+"([^"]+)"', attrs)),
                }
    if not out:
        raise ValueError("no ErdosProblems declarations found")
    return out, rev

# ---------- differs: each returns list of (tag, key, detail) ----------
def jsp_unclaimed(e): return e and e["status"] == "Solved" and e["lean"] == "No"
def diff_jsp(old, new):
    ev = []
    for k in sorted(set(old) | set(new)):
        o, n = old.get(k), new.get(k)
        if n is None:
            ev.append(("REMOVED", k, o["title"])); continue
        t = n["title"]
        if o is None:
            ev.append(("NEW ENTRY", k, f"{t} [status={n['status']}, lean={n['lean']}, eligible={n['eligible']}]"))
        else:
            if o["status"] != n["status"]:
                tag = "NEWLY SOLVED" if n["status"] == "Solved" else "STATUS CHANGED"
                ev.append((tag, k, f"{t} [{o['status']} -> {n['status']}]"))
            if o["eligible"] != n["eligible"]:
                tag = "NEWLY ELIGIBLE" if n["eligible"] == "Yes" else "ELIGIBILITY CHANGED"
                ev.append((tag, k, f"{t} [{o['eligible']} -> {n['eligible']}]"))
            if o["lean"] != n["lean"]:
                tag = "LEAN PROOF REMOVED" if n["lean"] == "No" else "LEAN PROOF ADDED (claimed)"
                ev.append((tag, k, f"{t} [{o['lean']} -> {n['lean']}]"))
            for u in sorted(set(o["lean_urls"]) - set(n["lean_urls"])):
                ev.append(("LEAN LINK REMOVED", k, f"{t} {u}"))
            if o["title"] != n["title"]:
                ev.append(("RETITLED", k, f"{o['title']} -> {t}"))
        if jsp_unclaimed(n) and not jsp_unclaimed(o):
            reason = jsp_filter_reason(k)
            if reason:
                ev.append(("NEWLY UNCLAIMED (CONTESTED)", k, f"{t} [eligible={n['eligible']}; {reason}]"))
            else:
                ev.append(("NEWLY UNCLAIMED (UNCONTESTED!)", k, f"{t} [eligible={n['eligible']}]"))
    return ev

def ep_base(s): return re.sub(r"\s*\(Lean\)$", "", s or "")
def ep_unclaimed(e): return e and ep_base(e.get("status")) in RESOLVED and e.get("formal_status") != "Lean"
def diff_erdos(old, new):
    ev = []
    for k in sorted(set(old) | set(new), key=lambda x: (len(x), x)):
        o, n = old.get(k), new.get(k)
        url = f"https://www.erdosproblems.com/{k}"
        if n is None:
            ev.append(("REMOVED", f"#{k}", url)); continue
        if o is None:
            ev.append(("NEW ENTRY", f"#{k}", f"status={n.get('status')} formal={n.get('formal_status')} {url}"))
        else:
            if o.get("status") != n.get("status"):
                tag = "NEWLY SOLVED" if ep_base(n.get("status")) in RESOLVED and ep_base(o.get("status")) not in RESOLVED else "STATUS CHANGED"
                ev.append((tag, f"#{k}", f"{o.get('status')} -> {n.get('status')} {url}"))
            if o.get("formal_status") != n.get("formal_status"):
                tag = "LEAN PROOF REMOVED" if o.get("formal_status") == "Lean" else "FORMAL STATUS CHANGED"
                ev.append((tag, f"#{k}", f"{o.get('formal_status')} -> {n.get('formal_status')} {url}"))
            if o.get("prize") != n.get("prize"):
                ev.append(("PRIZE CHANGED", f"#{k}", f"{o.get('prize')} -> {n.get('prize')} {url}"))
        if ep_unclaimed(n) and not ep_unclaimed(o):
            ev.append(("NEWLY UNCLAIMED (resolved, no Lean)", f"#{k}", f"{n.get('status')} prize={n.get('prize', '-')} {url}"))
    return ev

def fc_unclaimed(e): return e and e["category"] == "research solved" and e["sorry"] and not e["formal_proof"]
def diff_fc(old, new):
    ev = []
    for k in sorted(set(old) | set(new)):
        o, n = old.get(k), new.get(k)
        if n is None:
            ev.append(("REMOVED", k, f"was {o['category']}")); continue
        if o is None:
            if n["category"] == "research solved":
                ev.append(("NEW SOLVED STATEMENT", k, "has formal_proof" if n["formal_proof"] else ("sorry" if n["sorry"] else "proved in file")))
            else:
                ev.append(("NEW STATEMENT", k, n["category"]))
        else:
            if o["category"] != n["category"]:
                tag = "NEWLY SOLVED" if n["category"] == "research solved" else "CATEGORY CHANGED"
                ev.append((tag, k, f"{o['category']} -> {n['category']}"))
            for u in sorted(set(o["formal_proof"]) - set(n["formal_proof"])):
                ev.append(("FORMAL_PROOF LINK REMOVED", k, u))
            for u in sorted(set(n["formal_proof"]) - set(o["formal_proof"])):
                ev.append(("FORMAL_PROOF LINK ADDED (claimed)", k, u))
        if fc_unclaimed(n) and not fc_unclaimed(o):
            ev.append(("NEWLY UNCLAIMED (solved, sorry, no formal_proof)", k, ""))
    return ev

# ---------- driver ----------
def write_atomic(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=1, sort_keys=True, ensure_ascii=False)
        f.write("\n")
    os.replace(tmp, path)

sources = [
    ("jsp", "JSP catalog", os.path.join(work, "jsp"), parse_jsp, diff_jsp),
    ("erdos", "erdosproblems (teorth/erdosproblems)", os.path.join(work, "erdos.yaml"), parse_erdos, diff_erdos),
    ("fc", "formal-conjectures ErdosProblems", os.path.join(work, "fc.tgz"), parse_fc, diff_fc),
]
report, log_lines = [], []
for key, label, path, parse, differ in sources:
    if any(f.startswith(key + ":") for f in failed):
        continue
    snap_path = os.path.join(snap, f"{key}.json")
    try:
        new, rev = parse(path)
    except Exception as e:
        failed.append(f"{key}: parse failed: {e}"); continue
    old_doc = json.load(open(snap_path)) if os.path.exists(snap_path) else None
    if old_doc and len(new) < 0.5 * len(old_doc["entries"]):
        failed.append(f"{key}: only {len(new)} entries vs {len(old_doc['entries'])} in snapshot; refusing to update"); continue
    rev_s = f" @ {rev[:12]}" if rev else ""
    if old_doc is None:
        report.append(f"[{label}] baseline created: {len(new)} entries{rev_s}")
        write_atomic(snap_path, {"source": key, "updated": now, "rev": rev, "entries": new})
        continue
    ev = differ(old_doc["entries"], new)
    if ev:
        report.append(f"[{label}] {len(ev)} change(s) since {old_doc.get('updated')}{rev_s}:")
        for tag, k, detail in ev:
            line = f"  {tag:<34} {k}  {detail}".rstrip()
            report.append(line); log_lines.append(f"{now} {key} {line.strip()}")
    elif not quiet:
        report.append(f"[{label}] no changes ({len(new)} entries){rev_s}")
    if ev or rev != old_doc.get("rev"):
        write_atomic(snap_path, {"source": key, "updated": now, "rev": rev, "entries": new})

if log_lines:
    with open(os.path.join(snap, "changes.log"), "a", encoding="utf-8") as f:
        f.write("\n".join(log_lines) + "\n")
for f in failed:
    report.append(f"FAILED {f}")
if report:
    print(f"bounty_watch {now}")
    print("\n".join(report))
sys.exit(2 if failed else 0)
PY
rc=$?
set -e
if [[ $rc -ne 0 && -s "$WORK/err" && $QUIET -eq 0 ]]; then sed 's/^/  curl: /' "$WORK/err" >&2; fi
exit $rc
