"""Merge assessments with source data into a CSV. Usage: merge.py <data_open_aligned.json> <assess_dir> <jsp_all.json> <out.csv>"""
import json, glob, csv, re, sys
src, adir, jspf, out = sys.argv[1:5]
S = {e['number']: e for e in json.load(open(src))}
J = {j['id']: j for j in json.load(open(jspf))}
A = [a for f in sorted(glob.glob(f'{adir}/open_*.json')) for a in json.load(open(f))]
def usd(p):
    if not p or p == 'no': return 0
    m = re.search(r'[\d,]+', p); v = int(m.group(0).replace(',', '')) if m else 0
    return round(v * 1.3) if '£' in p else round(v / 85) if '₹' in p else v
rows = []
for a in A:
    s = S[str(a['number'])]; jid = a.get('jsp_id')
    jfile = J[jid]['file'] if jid in J else None
    d, fit = int(a['difficulty']), int(a['ai_lean_fit'])
    rows.append({
        'erdos_no': int(a['number']), 'prize': s['prize'] if s['prize'] != 'no' else '', 'prize_usd_approx': usd(s['prize']),
        'difficulty_1to5': d, 'ai_lean_fit_1to5': fit, 'tractability_score': (6 - d) + fit,
        'route': a['route'], 'area': a['area'], 'summary': a['summary'], 'stepping_stone': a['stepping_stone'],
        'possibly_resolved': 'yes' if a.get('possibly_resolved') else '', 'resolved_note': a.get('resolved_note', ''),
        'db_status': s['status'], 'lean_statement_in_formal_conjectures': s['lean_statement'],
        'jsp_id': jid or '', 'jsp_confidence': a.get('jsp_confidence', ''), 'jsp_bounty': a.get('jsp_bounty', ''),
        'tags': '; '.join(s['tags']), 'comments': s['comments'],
        'erdos_url': f"https://www.erdosproblems.com/{a['number']}",
        'formal_conjectures_url': f"https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/{a['number']}.lean" if s['lean_statement'] == 'yes' else '',
        'jsp_url': f"https://github.com/TheJustinSunPrize/awards/blob/main/problems/{jfile}#{jid}" if jfile else ''})
rows.sort(key=lambda r: (-r['tractability_score'], -r['prize_usd_approx'], r['erdos_no']))
with open(out, 'w', newline='') as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
missing = set(S) - {str(a['number']) for a in A}
print(len(rows), 'rows; missing:', sorted(missing, key=int)[:20])
