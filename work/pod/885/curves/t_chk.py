import json
from ratinterp import ratfit, pari
d=json.load(open("sfam.json"))
ts=[pari(o["s"])+9072 for o in d]
g=ratfit(ts,[pari(o["T0"]) for o in d])
for o,t in list(zip(d,ts))[:3]: print(t, pari(o["T0"]), pari.subst(g,'t',t))
print("T0(0)=",pari.subst(g,'t',0)*1.0)
