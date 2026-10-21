from obstr import setup, pari
rows=list(range(7)); cols=list(range(7))
inc,var,idx,Jm=setup(rows,cols)
K=pari.matker(Jm)
def rk(keys):
    M=pari.matrix(len(keys),len(K),[K[a][idx[k]] for k in keys for a in range(len(K))]); return pari.matrank(M)
c1=[("C",1,k) for k in range(5)]
print("rank on C1 coords",rk(c1))
for j in [0,2,4,5,6]:
    for k in range(5):
        print(j,k,rk(c1+[("C",j,k)]),end="; ")
print()
# also: ranks for C0,C1 coords
print("C0+C1",rk(c1+[("C",0,k) for k in range(5)]), "C1+C2",rk(c1+[("C",2,k) for k in range(5)]))
for pair in [(0,2),(0,3),(2,3),(0,1),(1,2),(0,4)]:
    keys=[("a",i,k) for i in pair for k in range(3)]
    print("rows",pair,"rank",rk(keys))
