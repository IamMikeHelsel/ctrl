"""Fetch statement/commentary for every open Erdős problem. Usage: fetch.py <yaml> <outdir> <out.json>"""
import sys, json, time, re, html, urllib.request, yaml, pathlib
ymlp, outdir, outjson = sys.argv[1:4]; MODE = sys.argv[4] if len(sys.argv) > 4 else "open"
OPEN = {'open','decidable','falsifiable','verifiable','not provable','not disprovable'}
ALL = yaml.safe_load(open(ymlp))
if MODE == 'open':
    P = [p for p in ALL if p['status']['state'].split(' (')[0] in OPEN]
else:  # solved informally but no Lean solution yet: formalizer targets
    P = [p for p in ALL if p['informal_status']['state'] in ('proved', 'disproved', 'solved') and p['formal_status']['state'] != 'Lean']
od = pathlib.Path(outdir)
def strip(s): return html.unescape(re.sub(r'\s+', ' ', re.sub(r'<[^>]+>', ' ', s))).strip()
rows = []
for p in P:
    n = p['number']; f = od / f'{n}.html'
    if not f.exists():
        req = urllib.request.Request(f'https://www.erdosproblems.com/{n}', headers={'User-Agent': 'erdos-assess research script (personal use)'})
        try: f.write_bytes(urllib.request.urlopen(req, timeout=30).read())
        except Exception as e: print(n, 'ERR', e, flush=True); continue
        time.sleep(1.0)
    h = f.read_text(errors='replace')
    stmt = re.search(r'<div id="content">(.*?)</div>', h, re.S)
    add = re.search(r'<div class="problem-additional-text">(.*?)<div class="problem-info">', h, re.S)
    com = re.search(r'Comments \((\d+)\)', h); cl = re.search(r'Proof claims \((\d+)\)', h)
    rows.append(dict(number=n, prize=p.get('prize','no'), status=p['status']['state'], formal_status=p['formal_status']['state'], tags=p.get('tags',[]),
        lean_statement=p['formalized']['state'], oeis=p.get('oeis',[]),
        statement=strip(stmt.group(1)) if stmt else '', notes=strip(add.group(1))[:3000] if add else '',
        comments=int(com.group(1)) if com else 0, proof_claims=int(cl.group(1)) if cl else 0))
json.dump(rows, open(outjson, 'w'), ensure_ascii=False, indent=1)
print('wrote', len(rows))
