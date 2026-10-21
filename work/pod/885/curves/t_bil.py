import cypari2
pari=cypari2.Pari()
t=pari('t')
den={"diag":t**2+64*t-15120,"two":2*t**2-61*t-15120}
F={"diag":{0:((24,7*t**3+2512*t**2+291360*t+10822896,5,1),(144,7*t**3+2416*t**2+256992*t+7756560,25)),
           2:((72,t**2-4661*t-619920,1,1),(1296,41*t**2+5459*t-136080,1)),
           3:((32,5*t**3+1324*t**2+111056*t+3709620,21,1),(256,5*t**3+1396*t**2+114224*t+2188620,441))},
   "two":{0:((24,28*t**3+6046*t**2+440403*t+10822896,5,1),(144,28*t**3+5602*t**2+365997*t+7756560,25)),
          2:((144,t**2-4283*t-309960,1,1),(5184,41*t**2+2057*t-68040,1)),
          3:((8,40*t**3+7667*t**2+549769*t+14838480,21,1),(16,40*t**3+8333*t**2+515191*t+8754480,441))}}
for sl in ("diag","two"):
    D=den[sl]
    for i,((cP,nP,dP,_),(cQ,nQ,dQ)) in F[sl].items():
        P=pari(cP)*nP/(pari(dP)*D)
        rQ=pari.sqrtint(cQ)*nQ/(pari.sqrtint(dQ)*D)
        for sg in (1,-1):
            c=-P+2*sg*rQ
            print(sl,"row",i,sg, pari.factor(pari.numerator(c)), "/", pari.factor(pari.denominator(c)), "const", pari.content(pari.numerator(c)), pari.content(pari.denominator(c)))
