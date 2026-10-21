import warnings; warnings.filterwarnings('ignore')
import numpy as np
from core import *
from classes import g_class
from e07_dual_at import top_pair
rng = np.random.default_rng(0)
pairs = [('ssfail',)+top_pair(np.load('logs/e05_n6_s1_e0.05_best.npy'))[:2], ('ssfail2',)+top_pair(np.load('logs/e05_n6_s2_e0.05_best.npy'))[:2]]
for k in range(5): pairs.append(('gauss',)+random_pair(rng)[:2])
for k in range(3): pairs.append(('nat',)+top_pair(rng.standard_normal((6,6)))[:2])
for lab,K,Y in pairs:
    r = {nm: g_class(K,Y,nm)[0] for nm in ['C6K','C9K','C9Y','C9K+C9Y','full']}
    rl = g_class(K,Y,'C9Y',side='left')[0]
    print(lab, {k: round(v,6) for k,v in r.items()}, 'C9Y-left', round(rl,6), flush=True)
