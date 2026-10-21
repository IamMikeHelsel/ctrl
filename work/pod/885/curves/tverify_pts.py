import json, sys
from families import pari
from polyrows import poly_rows
d=json.load(open('poly77_lagrange.json'))
C1L=pari(d['C'][1]); C2L=pari(d['C'][2])
W1=pari('2*x^2+6*x+7'); W2=pari('4*x^2+10*x+1')
pts=[l.split() for l in open(sys.argv[1]) if l.startswith("HIT")]
out=[]
for P in pts:
    a=pari(P[1][2:]); b=pari(P[2][2:])
    t1=125-5*a**2; t2=21*b**2-189
    C1=C1L+t1*W1**2; C2=C2L+t2*W2**2
    if C1==0 or C2==0 or C1==C2 or pari.poldegree(C1)<0: print("degenerate",t1,t2); continue
    R=poly_rows([C1,C2,pari(0)],2)
    rows=[X for k,(X,s) in R.items() if len(s)==3]
    # dual: columns valid on 3 rows chosen: all rows found
    cols=[]
    if len(rows)>=3:
        for tri in [rows[:3]]:
            Cc=poly_rows(rows,2)
            cols=[X for k,(X,s) in Cc.items() if len(s)==len(rows)]
    print(f"t1={t1} t2={t2}: rows on {{C1,C2,0}}: {len(rows)}; cols valid on all those rows: {len(cols)}; C1 {pari.factor(C1)[0]} C2 {pari.factor(C2)[0]}",flush=True)
    out.append({"t1":str(t1),"t2":str(t2),"C1":str(C1),"C2":str(C2),"rows":[str(x) for x in rows]})
json.dump(out,open("spoints.json","w"))
