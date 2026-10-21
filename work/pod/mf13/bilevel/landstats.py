import numpy as np
for fn in ('landscape_gauss_101.npy','landscape_fromA_102.npy'):
    r = np.load(fn); f = r[:,0]
    print(fn, "N", len(f), "quantiles(0,1,5,10,25,50,75,90,100%):", np.round(np.quantile(f,[0,.01,.05,.1,.25,.5,.75,.9,1]),5))
    sK = r[:,1]; 
    for lo,hi in ((0,1e-3),(1e-3,1e-2),(1e-2,0.05),(0.05,0.1),(0.1,0.5)):
        m = (sK>=lo)&(sK<hi)
        if m.sum(): print(f"   sigma_min(K) in [{lo},{hi}): n={m.sum():4d} min f-1={f[m].min()-1:.2e} median f-1={np.median(f[m])-1:.2e}")
    print("   corr(log(f-1), log sK) =", np.corrcoef(np.log(f-1+1e-16), np.log(sK))[0,1])
    print("   frac f<1.01:", (f<1.01).mean(), " frac f<1.001:", (f<1.001).mean(), " count f<1:", (f<1).sum())
