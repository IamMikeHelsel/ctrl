import cypari2
pari=cypari2.Pari()
m,k,y=pari('m'),pari('k'),pari('y')
m0=pari('179/39'); y0=pari('630/39')
assert y0**2==21*(189*m0**2-1248*m0+1759)
# line y = y0 + k (m - m0)
eq=21*(189*m**2-1248*m+1759)-(y0+k*(m-m0))**2
lin=pari.numerator(eq/(m-m0)); lin=pari.factor(lin)
print(lin)
