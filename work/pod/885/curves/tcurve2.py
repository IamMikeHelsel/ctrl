import cypari2
pari=cypari2.Pari(); pari.allocatemem(2*10**9)
A,k=pari('A'),pari('k')
# conic B^2 - 21 A^2 = 945 through (A,B)=(12,63): B = 63 + k (A - 12)
eq=(63+k*(A-12))**2-21*A**2-945
lin=pari.numerator(eq/(A-12)); 
Ak=-pari.polcoef(lin,0,'A')/pari.polcoef(lin,1,'A')
print("A(k) =",Ak)
q=21*Ak**2-320
Q=pari.numerator(q)*pari.denominator(q)
print("C^2 = ", pari.factor(Q), " content", pari.content(Q))
quart=pari('676*x^4 - 15876*x^3 + 118461*x^2 - 333396*x + 298116')
E=pari.ellinit(pari.ellfromeqn(pari('y^2')-quart))
Em=pari.ellminimalmodel(E)
print("E:",[Em[i] for i in range(5)],"cond",pari.ellglobalred(Em)[0],"tors",pari.elltors(Em))
r=pari.ellrank(Em); print("rank bounds",r[0],r[1],"gens",r[3])
