import cypari2
pari=cypari2.Pari(); pari.allocatemem(2*10**9)
# conic (t+144)(21t+2704) = y^2 through (t,y)=(0,624): line y = 624 + m t
t=pari('t'); m=pari('m')
eq=(t+144)*(21*t+2704)-(624+m*t)**2
sol=pari.factor(pari.numerator(eq/t))  # linear in t after dividing by t
print(sol)
lin=pari.numerator(eq/t)
tm=-pari.polcoef(lin,0,'t')/pari.polcoef(lin,1,'t')
print("t(m) =",tm)
q=21*(tm+144)*(tm+189)*(21*tm+2704)**0
Q=pari.numerator(q)*pari.denominator(q)
print("quartic in m:",pari.factor(Q))
# 21(t+189)(21t+2704) square given (t+144)(21t+2704) square <=> 21(t+144)(t+189) square
q2=21*(tm+144)*(tm+189); Q2=pari.numerator(q2)*pari.denominator(q2)
fa=pari.factor(Q2); print("Q2:",fa)
core=1
for i in range(len(fa[0])):
    if int(fa[1][i])%2: core*=fa[0][i]
c=pari.content(core); core=core/c; c=pari.core(pari.numerator(c)*pari.denominator(c))
print("y^2 =",c,"*",core, "deg",pari.poldegree(core,'m'))
E=pari.ellfromeqn(pari('y^2')-c*pari.subst(core,'m',pari('x')))
E=pari.ellinit(E); print("E:",E[:5],"j",E[12]); 
Em=pari.ellminimalmodel(E); print("minimal",Em[:5],"conductor",pari.ellglobalred(Em)[0],"tors",pari.elltors(Em)[1])
r=pari.ellrank(Em); print("rank",r[:3],"gens",r[3])
