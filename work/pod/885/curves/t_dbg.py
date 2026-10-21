from families import pari, load
from polyrows import divisors_monic, solve_pair, vec
U,V=load('lagrange',{'u':'x','v':'1'})
z=pari('6*(x^2+13*x+16)')
for j in (1,2,3):
    w2=z*z+V[j]; ok=pari.issquare(w2); w=pari.sqrt(w2) if False else None
    # find w
    import cypari2
    w=pari(f"my(h);issquare({w2},&h);h")
    for s in (1,-1):
        A=w*s-z
        print(j, s, pari.factor(A), pari.poldegree(A))
