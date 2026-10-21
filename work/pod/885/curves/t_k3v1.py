import json
from k3height import K3, pari
d=json.load(open('poly77_v1.json'))
R,C=d['R'],d['C']
B=[0,1,2]
E=K3([C[j] for j in B])
print({k:v[:2] for k,v in E.types.items()})
Ps=[E.half(r) for r in R]
G=E.gram(Ps)
for row in G: print([str(g) for g in row])
M=pari.matrix(7,7,[str(g) for row in G for g in row]); print("rank",pari.matrank(M),"det-ish", pari.matdet(M))
# torsion heights sanity
T=[pari([wt:=0]) for _ in []]
