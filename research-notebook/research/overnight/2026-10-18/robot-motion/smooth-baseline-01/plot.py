"""Plot saved data only; this script does not generate plans or physical states."""
from pathlib import Path
import csv,gzip,hashlib,json,sys
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'builder-03'
methods=[('native_fast','Native fast','#697683'),('native_matched','Native matched','#b77727'),
         ('fir_checked','Checked FIR','#3368a6'),('smooth_n90_cap10mm','Smooth / 10 mm cap','#087f6f')]
inputs=[]
def load(path):
    inputs.append(path)
    with gzip.open(path,'rt') as f:return [{k:(v if k in ['side','labels','time_exact'] else float(v)) for k,v in row.items()} for row in csv.DictReader(f)]
rows=json.loads((HERE/'metrics.json').read_text())['rows']+json.loads((BASE/'metrics.json').read_text())['rows']
fig=plt.figure(figsize=(12,9),layout='constrained')
grid=fig.add_gridspec(2,2,height_ratios=[1.25,1])
axpos=fig.add_subplot(grid[0,0]);axjerk=fig.add_subplot(grid[0,1]);axtrade=fig.add_subplot(grid[1,0]);axpeak=fig.add_subplot(grid[1,1])
for method,label,color in methods:
    folder=HERE if method.startswith('smooth') else BASE
    data=load(folder/'traces'/f'return_generous__{method}__r100__w00__dt500us.csv.gz')
    data=[r for r in data if .5<=r['time_s']<=1.8] if 'time_s' in data[0] else [r for r in data if .5<=float(__import__('fractions').Fraction(r['time_exact']))<=1.8]
    t=[float(__import__('fractions').Fraction(r['time_exact'])) for r in data]
    axpos.plot(t,[1000*r['x'] for r in data],label=label,color=color,lw=1.8)
    axjerk.plot(t,[r['actual_jerk'] for r in data],label=label,color=color,lw=1.5)
    group=[r for r in rows if r['method']==method and r['case']=='return_generous' and r['sample_step_s']==.0005]
    axtrade.scatter([r['suffix_until_horizon_extra_forward_excursion_m']*1000 for r in group],
                    [r['suffix_until_horizon_jerk_energy_m2_s5'] for r in group],s=38,color=color,label=label)
    index=[m[0] for m in methods].index(method)
    values=[r['suffix_until_horizon_actual_jerk_peak_m_s3'] for r in group]
    axpeak.plot([index,index],[min(values),max(values)],lw=5,color=color,solid_capstyle='round')
    axpeak.scatter([index]*len(values),values,color=color,s=22)
for ax in [axpos,axjerk]:
    ax.axvline(.52,color='#777',ls=':',lw=1)
    ax.axvline(1.42,color='#777',ls=':',lw=1)
    ax.set_xlabel('Time (s)')
axpos.axhspan(-.2,.2,color='#087f6f',alpha=.12)
axpos.set_ylabel('Actual position (mm)');axpos.set_title('One declared plant: response 100/s, disturbance 0')
axjerk.set_ylabel('Actual jerk (m/s³)');axjerk.set_title('A lower integral can still have a higher peak')
axtrade.set_xlabel('Maximum extra forward travel (mm)');axtrade.set_ylabel('Integral of actual jerk² (m²/s⁵)')
axtrade.set_title('All six plant cases; suffix 0.52–2.50 s')
axpeak.set_xticks(range(4),['Native\nfast','Native\nmatched','Checked\nFIR','Smooth\n10 mm cap'])
axpeak.set_ylabel('Peak actual jerk (m/s³)');axpeak.set_title('Peak jerk on the same suffix')
for ax in [axpos,axjerk,axtrade,axpeak]:
    ax.grid(alpha=.18);ax.spines[['top','right']].set_visible(False)
axpos.legend(fontsize=8,loc='upper right')
fig.suptitle('Which kind of smoothness does the task need?',fontsize=18,fontweight='bold')
fig.savefig(HERE/'smooth-comparison.png',dpi=170)
fig.savefig(HERE/'smooth-comparison.svg')
(HERE/'figure-runtime.json').write_text(json.dumps({'python':sys.version,'executable':sys.executable,'matplotlib':matplotlib.__version__,'scope':'saved data rendering only','files':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}},indent=2)+'\n')
