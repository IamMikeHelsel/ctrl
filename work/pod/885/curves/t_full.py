import sys
from sfam import data, pari
from algdeg import degof
s=pari(sys.argv[1])
o,z=data(s)
for i in range(7):
    d,p=degof(z[("a",i,2)],8); print("a",i,"lead deg",d, pari.factor(p)[0] if d else "", "core disc" , pari.core(pari.poldisc(p)) if d==2 else "")
