"""Shortlist JSP candidates for each open Erdős problem via TF-IDF + bounty agreement.
Usage: match.py <data_open.json> <jsp_open.json> <out.json>"""
import json, re, sys
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.metrics.pairwise import cosine_similarity
E = json.load(open(sys.argv[1])); J = json.load(open(sys.argv[2]))
def clean(s): return re.sub(r'\\[a-zA-Z]+|[${}^_\\]', ' ', s).lower()
def money(s):
    m = re.search(r'[\d,]+', s or ''); return m.group(0).replace(',', '') if m else None
vec = TfidfVectorizer(ngram_range=(1, 2), min_df=1, stop_words='english', sublinear_tf=True)
X = vec.fit_transform([clean(e['statement'] + ' ' + ' '.join(e['tags'])) for e in E] +
                      [clean(j['title'] + ' ' + j['description'] + ' ' + j['area']) for j in J])
S = cosine_similarity(X[:len(E)], X[len(E):])
for i, e in enumerate(E):
    sc = S[i].copy()
    em = money(e['prize']) if e['prize'] != 'no' else None
    for k, j in enumerate(J):
        if em and money(j['bounty']) == em: sc[k] += 0.15
    top = sc.argsort()[::-1][:5]
    e['jsp_candidates'] = [dict(id=J[k]['id'], score=round(float(sc[k]), 3), bounty=J[k]['bounty'][:30],
                                title=J[k]['title'][:160]) for k in top]
json.dump(E, open(sys.argv[3], 'w'), ensure_ascii=False, indent=1)
print('matched', len(E))
