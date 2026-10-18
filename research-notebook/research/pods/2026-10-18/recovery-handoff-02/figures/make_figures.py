"""Illustrations from declared scalar equations; no numerical proof claim."""
from pathlib import Path
import hashlib,json,math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

HERE=Path(__file__).resolve().parent
plt.rcParams.update({'font.size':11,'axes.spines.top':False,'axes.spines.right':False,'axes.titleweight':'bold','font.family':'DejaVu Sans','svg.fonttype':'none','svg.hashsalt':'recovery-handoff-02'})
colors=['#126782','#bd6b00','#7d4ba7']
fig,axs=plt.subplots(2,1,figsize=(10,7.4),sharex=True,layout='constrained')
t=np.linspace(0,.6,1201)
for rate,col in zip((8,10,12),colors):
 states=[]
 for tt in t:
  if tt<=.05:
   x=.001+.41*tt+.1*tt*tt/2; v=.41+.1*tt
  else:
   s=tt-.05;e=math.exp(-rate*s)
   x=.021625+.415*s-1.2*s*s/2+1.3*(s/rate-(1-e)/rate**2)
   v=.415-1.2*s+1.3*(1-e)/rate
  states.append((1000*x,1000*v))
 a=np.array(states)
 axs[0].plot(t,a[:,0],color=col,label=f'Response rate {rate}/s',lw=2.1)
 axs[1].plot(t,a[:,1],color=col,lw=2.1)
axs[0].axhspan(139,141,color='#bd3b45',alpha=.15)
axs[0].axhline(139,color='#bd3b45',ls=':',lw=1)
axs[0].text(.025,143,'New fixed admission requires position 139–141 mm',color='#93313b',fontsize=10)
axs[0].set(ylabel='Position (mm)',ylim=(0,155),title='Safe stopping does not ensure that a fixed handoff box is reached')
axs[0].legend(loc='lower right',frameon=False,ncol=1)
axs[1].axhspan(-20,0,color='#bd3b45',alpha=.15)
axs[1].axhline(0,color='#bd3b45',ls=':',lw=1)
axs[1].text(.02,-58,'New fixed admission also requires velocity −20 to 0 mm/s',color='#93313b',fontsize=10)
axs[1].set(xlabel='Time from the start of the stop (s)',ylabel='Velocity (mm/s)',ylim=(-160,460))
for ax in axs:
 ax.axvline(.05,color='#666',ls='--',lw=1)
 ax.grid(alpha=.18)
fig.suptitle('Same initial state; three allowed response rates',fontsize=17)
fig.text(.01,-.035,'Illustration only: x₀=1 mm, v₀=410 mm/s, a₀=0.1 m/s². Target q=0.1 for 50 ms, then −1.2 m/s².\nExact held-flow formulas evaluated numerically. No handoff occurs here. Admission also requires a between −1.22 and −1.12 m/s². No hardware result.',fontsize=9)
for ext in ('svg','png'):
 fig.savefig(HERE/f'admission-gap.{ext}',dpi=160,bbox_inches='tight',metadata={'Date':None} if ext=='svg' else None)
plt.close(fig)

fig,ax=plt.subplots(figsize=(10,4.4),layout='constrained')
b=np.linspace(.02,2,600)
L=(.01+b/8)**2/(2*b)
ax.plot(b,1000*L,color=colors[0],lw=2.3)
ax.scatter([.08,1,2],[2.5,9.1125,16.9],color=colors[1],zorder=3)
ax.annotate('2.5 mm',(.08,2.5),xytext=(.22,5),arrowprops={'arrowstyle':'-','color':'#777'})
ax.annotate('9.1125 mm',(1,9.1125),xytext=(.8,13),arrowprops={'arrowstyle':'-','color':'#777'})
ax.annotate('16.9 mm',(2,16.9),xytext=(1.55,19),arrowprops={'arrowstyle':'-','color':'#777'})
ax.set(title='A loose bound can get worse when the assumed brake gets stronger',xlabel='Recovered effective braking lower bound b (m/s²)',ylabel='Simple forward-travel bound (mm)',ylim=(0,21))
ax.grid(alpha=.18)
fig.text(.01,-.065,'Algebraic screen: initial speed 10 mm/s, A=T=0, response floor 8/s. Curve is L=(v₀+b/λ)²/(2b).\nThis is conservatism from a dropped exponential term. It does not show that stronger physical brakes are worse.',fontsize=9)
for ext in ('svg','png'):
 fig.savefig(HERE/f'bound-conservatism.{ext}',dpi=160,bbox_inches='tight',metadata={'Date':None} if ext=='svg' else None)
plt.close(fig)
fig,axs=plt.subplots(2,1,figsize=(10,5.2),sharex=True,sharey=True,layout='constrained')
for ax,period,col in zip(axs,(.5,1.0),colors):
 latency=.2
 for n in range(7):
  sample=n*period; start=sample+latency; end=min(sample+period+latency,3.2)
  if start>=3.2: break
  ax.plot([start,end],[latency,end-sample],color=col,lw=2.5)
  ax.scatter([start],[latency],color=col,s=17,zorder=4)
  ax.scatter([end],[end-sample],facecolors='white',edgecolors=col,s=22,zorder=4)
 ax.axhspan(1,1.35,color='#bd3b45',alpha=.12)
 ax.axhline(1,color='#bd3b45',ls='--',lw=1)
 ax.set(title=f'Sample period {period:g} ms + dispatch delay 0.2 ms → peak age {period+.2:g} ms',ylabel='Reading age (ms)',ylim=(0,1.35))
 ax.grid(alpha=.17)
axs[1].set_xlabel('Time on one shared clock (ms)')
fig.suptitle('A 1 ms sample period is not a 1 ms age bound',fontsize=17)
fig.text(.01,-.055,'Clock illustration only. Open dots show the old reading just before a command change. Filled dots show the new reading.\nThe top schedule meets the age condition; the bottom does not. Passing this condition alone does not establish safety.',fontsize=9)
for ext in ('svg','png'):
 fig.savefig(HERE/f'total-reading-age.{ext}',dpi=160,bbox_inches='tight',metadata={'Date':None} if ext=='svg' else None)
plt.close(fig)

report={'status':'Numerical and algebraic illustrations, not proof or hardware evidence','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'matplotlib':matplotlib.__version__,'numpy':np.__version__,'files':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted([*HERE.glob('*.svg'),*HERE.glob('*.png')])}}
(HERE/'figure-provenance.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
