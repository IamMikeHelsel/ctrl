from pathlib import Path
from fractions import Fraction
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np
BASE=Path(__file__).resolve().parent
c=json.loads((BASE/'frozen-candidate.json').read_text())
asfloat=lambda values:np.array([float(Fraction(v)) for v in values])
k=asfloat(c['knots']);r=asfloat(c['rate']);w=asfloat(c['disturbance'])
d=np.load(BASE/'dop853-traces.npz');t=d['times'];y=d['scaled_states'][:,:,0]
fig,ax=plt.subplots(3,1,figsize=(10,8),layout='constrained',sharex=True)
fig.suptitle('Strongest sampled case: changing response and disturbance',fontsize=15)
ax[0].plot(k,r,color='#155e75');ax[0].set_ylabel('Response rate r (1/s)');ax[0].set_ylim(75,125)
ax[1].plot(k,w,color='#9a3412');ax[1].set_ylabel('Disturbance w (m/s²)');ax[1].set_ylim(-.011,.011)
ax[2].plot(t,40000*y[:,1],label='Velocity / 0.001 m/s',color='#155e75')
ax[2].plot(t,80000*y[:,2],label='Acceleration / 0.02 m/s²',color='#9a3412')
ax[2].axhline(1,color='gray',linestyle='--');ax[2].axhline(-1,color='gray',linestyle='--')
ax[2].set_ylim(-1.1,1.1);ax[2].set_ylabel('Signed fraction of limit');ax[2].set_xlabel('Hold time (s)')
ax[2].legend(loc='upper left');ax[2].set_xlim(2,4)
for a in ax:a.grid(alpha=.2)
fig.text(.01,-.015,'Fixed candidate; independent numerical replay. No all-input or all-time certificate. '
         'Initial state: x−c = −0.2 mm, v = a = 0.',fontsize=10)
fig.savefig(BASE/'strongest-case.svg',bbox_inches='tight');fig.savefig(BASE/'strongest-case.png',dpi=150,bbox_inches='tight')
