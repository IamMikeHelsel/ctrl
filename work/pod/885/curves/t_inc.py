import json
from families import pari
d=json.load(open('poly77_lagrange.json'))
R=[pari(r) for r in d['R']];C=[pari(c) for c in d['C']]
print("   "+"".join(str(j) for j in range(7)))
for i,r in enumerate(R):
    print(i,":","".join("1" if pari.issquare(r+c) else "." for c in C), pari.factor(r))
for j,c in enumerate(C): print("C",j,pari.factor(c) if c!=0 else 0)
