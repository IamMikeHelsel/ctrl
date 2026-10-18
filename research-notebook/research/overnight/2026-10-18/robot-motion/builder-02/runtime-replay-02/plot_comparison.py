"""Saved-data illustration only; no simulation or parameter changes."""
from pathlib import Path
import csv,gzip,hashlib,json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent
manifest=json.loads((HERE/'data-sha256.json').read_text())['files']
methods=[('ruckig','Native fast','#1559aa'),('ruckig_min_08','Native minimum 0.8 s','#7958aa'),('fir','Old jerk-only FIR','#c44539'),('fir_checked','Checked delayed FIR','#007f73')]
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':11,'axes.spines.top':False,'axes.spines.right':False,'axes.grid':True,'grid.alpha':.18})
fig,axes=plt.subplots(2,1,figsize=(10,7.2),sharex=True,layout='constrained')
inputs={}
for method,label,color in methods:
    name=f'traces/return_generous__{method}__r100__w01__dt500us.csv.gz';path=HERE/name
    digest=hashlib.sha256(path.read_bytes()).hexdigest();assert digest==manifest[name];inputs[name]=digest
    with gzip.open(path,'rt') as f:rows=list(csv.DictReader(f))
    times=[float(r['time_s']) for r in rows];x=[1000*float(r['x']) for r in rows];j=[float(r['actual_jerk']) for r in rows]
    axes[0].plot(times,x,label=label,color=color,lw=1.8)
    axes[1].plot(times,j,color=color,lw=1.5)
axes[0].axhspan(-.2,.2,color='#007f73',alpha=.1)
axes[0].set_ylabel('Actual position (mm)');axes[0].legend(frameon=False,loc='upper right',fontsize=9)
axes[1].set_ylabel('Actual jerk (m/s³)');axes[1].set_xlabel('Time (s)')
for ax in axes:
    ax.set_xlim(0,1.75);ax.axvline(.5,color='#555',ls=':',alpha=.7);ax.axvline(1.7,color='#555',ls='--',alpha=.7)
axes[0].annotate('Revised goal issued',(0.5,0),xytext=(.08,-3),arrowprops={'arrowstyle':'-','color':'#555'},fontsize=10)
axes[0].annotate('Deadline',(1.7,0),xytext=(1.49,7),arrowprops={'arrowstyle':'-','color':'#555'},fontsize=10)
fig.suptitle('The checked delay trades response time for reference limits\nSaved scalar-plant traces · rate 100 /s · disturbance 0.01 m/s²',fontsize=13,fontweight='bold')
fig.supxlabel('Different actual states at revision: these curves do not isolate a matched-path jerk benefit.',fontsize=10)
fig.savefig(HERE/'physical-comparison.png',dpi=170);fig.savefig(HERE/'physical-comparison.svg')
(HERE/'figure-inputs.json').write_text(json.dumps({'scope':'One declared illustrative parameter case, saved finite numerical data only','files':inputs},indent=2)+'\n')
