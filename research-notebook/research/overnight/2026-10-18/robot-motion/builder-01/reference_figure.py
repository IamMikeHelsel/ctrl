"""Illustration of the proved reference histories; not a physical simulation."""
from pathlib import Path
import csv,json,math
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent
COEFF=(1,-4,6,-4,1)
def kernel(order,z):
    if z<=0:return 0.
    if z>=4:return 1. if order==0 else 0.
    n=4-order
    return sum(c*max(z-k,0.)**n for k,c in enumerate(COEFF))/math.factorial(n)
def jet(t,tau):
    return [sum(d*kernel(k,(t-e)/.2)/.2**k for e,d in [(.22,.02),(tau,-.02)]) for k in range(4)]
ts=np.unique(np.concatenate([np.linspace(0,1.7,1701),[.22,.52,.62,.77,1.32,1.42,1.7]]))
y={name:np.array([jet(float(t),tau) for t in ts]) for name,tau in [('Immediate return',.52),('Checked delayed return',.62)]}
with (HERE/'reference-points.csv').open('w',newline='') as f:
    w=csv.writer(f);w.writerow(['reference','time_s','position_m','velocity_m_s','acceleration_m_s2','jerk_m_s3'])
    for name,values in y.items():
        for t,row in zip(ts,values):w.writerow([name,format(t,'.17g'),*[format(v,'.17g') for v in row]])
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':11,'axes.spines.top':False,'axes.spines.right':False,'axes.grid':True,'grid.alpha':.17})
fig,axs=plt.subplots(2,1,figsize=(10,7),sharex=True,layout='constrained')
colors={'Immediate return':'#c43c39','Checked delayed return':'#007d89'}
for name,values in y.items():
    axs[0].plot(ts,1000*values[:,0],label=name,color=colors[name],lw=2)
    axs[1].plot(ts,values[:,2],color=colors[name],lw=2)
axs[0].set_ylabel('Reference position (mm)');axs[0].legend(frameon=False,loc='upper right')
axs[1].axhspan(-.5,.5,color='#12717b',alpha=.06)
for v in [-.5,.5]:axs[1].axhline(v,color='#505862',ls='--',lw=1)
axs[1].scatter([.77],[-21/32],color='#c43c39',zorder=6)
axs[1].annotate('Exact violation: −21/32 m/s²',(.77,-21/32),xytext=(.88,-.77),arrowprops={'arrowstyle':'-','color':'#c43c39'},color='#9e2528')
axs[1].set_ylim(-.83,.61);axs[1].set_ylabel('Reference acceleration (m/s²)');axs[1].set_xlabel('Time (s)')
for ax in axs:
    ax.set_xlim(0,1.72)
    ax.axvline(.52,color='#c43c39',alpha=.3,ls=':')
    ax.axvline(.62,color='#007d89',alpha=.4,ls=':')
    ax.axvline(1.42,color='#007d89',alpha=.4,ls=':')
    ax.axvline(1.7,color='#505862',ls='--',alpha=.6)
axs[0].annotate('Ready at 0.52 s\nExecute at 0.62 s',(.62,float(y['Checked delayed return'][np.argmin(abs(ts-.62)),0])*1000),xytext=(.35,18.5),arrowprops={'arrowstyle':'-','color':'#007d89'},color='#00626b')
axs[0].annotate('Reference rests by 1.42 s\nDeadline: 1.70 s',(1.42,0),xytext=(1.02,10),arrowprops={'arrowstyle':'-','color':'#007d89'},color='#00626b')
fig.suptitle('Wait 100 ms, keep the old motion, meet the reference limits\nReference trajectories only · physical motion still needs a separate proof',fontsize=14,fontweight='bold')
fig.savefig(HERE/'reference-comparison.png',dpi=170)
fig.savefig(HERE/'reference-comparison.svg')
(HERE/'figure-metadata.json').write_text(json.dumps({'scope':'Illustration only, floating point samples, no physical simulation','rows':len(ts)*2,'old_history_s_m':[[.22,.02],[.52,-.02]],'new_history_s_m':[[.22,.02],[.62,-.02]],'filter_width_s':.2,'acceleration_limit_m_s2':.5,'deadline_s':1.7},indent=2)+'\n')
