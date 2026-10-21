from sfam import data, pari
for s in ["-9072","-90719/10","-9071"]:
    o,z=data(pari(s)); print(s, o["T0"], pari(o["T0"])*1.0, o["N0"])
