import cProfile, pstats
from ext import search_curve
from known import KNOWN
U,V=KNOWN["lagrange44"]
cProfile.run("search_curve(V[:3], Nrow=2, K=9, Ncol=2, extra_rows=U)", "/tmp/prof")
pstats.Stats("/tmp/prof").sort_stats("tottime").print_stats(8)
