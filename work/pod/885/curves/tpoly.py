import json
from families import pari
from polyrows import poly_rows
d=json.load(open('poly77_lagrange.json'))
C1=pari(d['C'][1]); C2L=pari(d['C'][2]); w=pari('4*x^2+10*x+1')
def t_of_k(k):
    k=pari(k); m=-(-179*k**2+1260*k+311661)/(39*k**2-154791)
    return (-1248*m+5728)/(m**2-21)
for k in ["1000","100","3","1/2","7/3"]:
    t=t_of_k(k)
    C2=C2L+t*w**2
    V=[C1,C2,pari(0)]
    R=poly_rows(V,2)
    print("k",k,"t",t,"C2 factor",pari.factor(C2)[0], "#rows valid on all 3:",sum(1 for kk,(X,s) in R.items() if len(s)==3), flush=True)
    for kk,(X,s) in R.items():
        if len(s)==3: print("    ",pari.factor(X))
