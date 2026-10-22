"""Order-preserving alignment of open Erdős problems to the full JSP catalog.
Usage: align.py <data_open_matched.json> <jsp_all.json> <out.json>"""
import json, re, sys
import numpy as np
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.metrics.pairwise import cosine_similarity
E = json.load(open(sys.argv[1])); J = json.load(open(sys.argv[2]))
E.sort(key=lambda e: int(e['number'])); J.sort(key=lambda j: j['id'])
def clean(s): return re.sub(r'\\[a-zA-Z]+|[${}^_\\]', ' ', s).lower()
def money(s):
    m = re.search(r'[\d,]+', s or ''); return m.group(0).replace(',', '') if m else None
v = TfidfVectorizer(ngram_range=(1, 2), stop_words='english', sublinear_tf=True)
X = v.fit_transform([clean(e['statement'] + ' ' + ' '.join(e['tags'])) for e in E] + [clean(j['title'] + ' ' + j['description'] + ' ' + j['area']) for j in J])
S = cosine_similarity(X[:len(E)], X[len(E):])
for i, e in enumerate(E):
    em = money(e['prize']) if e['prize'] != 'no' else None
    if em:
        for k, j in enumerate(J):
            if money(j['bounty']) == em: S[i, k] += 0.15
T = 0.08  # minimum similarity for a pairing to count
n, m = S.shape; D = np.zeros((n + 1, m + 1)); B = np.zeros((n + 1, m + 1), dtype=np.int8)
for i in range(1, n + 1):
    for k in range(1, m + 1):
        opts = (D[i-1, k], D[i, k-1], D[i-1, k-1] + (S[i-1, k-1] - T))
        b = int(np.argmax(opts)); D[i, k] = opts[b]; B[i, k] = b
i, k, pairs = n, m, {}
while i > 0 and k > 0:
    b = B[i, k]
    if b == 2: pairs[i-1] = k-1; i -= 1; k -= 1
    elif b == 0: i -= 1
    else: k -= 1
for i, e in enumerate(E):
    if i in pairs:
        j = J[pairs[i]]; e['jsp_aligned'] = dict(id=j['id'], status=j['status'], bounty=j['bounty'][:40], score=round(float(S[i, pairs[i]]), 3), title=j['title'][:160])
    else: e['jsp_aligned'] = None
json.dump(E, open(sys.argv[3], 'w'), ensure_ascii=False, indent=1)
sc = [e['jsp_aligned']['score'] for e in E if e['jsp_aligned']]
print('aligned', len(sc), 'of', len(E), 'median score', round(float(np.median(sc)), 3), 'low(<.15):', sum(s < .15 for s in sc))
