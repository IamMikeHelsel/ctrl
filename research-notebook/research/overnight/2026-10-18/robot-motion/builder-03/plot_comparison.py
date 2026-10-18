from pathlib import Path
import csv,gzip,json,hashlib
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
HERE=Path(__file__).resolve().parent
COLORS={'fir_checked':'#007f84','native_fast':'#c35a2d','native_matched':'#7753b9'}
NAMES={'fir_checked':'Retained FIR','native_fast':'Native fast','native_matched':'Native matched'}
METHODS=list(COLORS)
summary=json.loads((HERE/'comparison-summary.json').read_text())['rows'];inputhash={}
def trace(case,method):
 p=HERE/'traces'/f'{case}__{method}__r100__w01__dt500us.csv.gz';inputhash[str(p.relative_to(HERE))]=hashlib.sha256(p.read_bytes()).hexdigest()
 with gzip.open(p,'rt') as f:rs=list(csv.DictReader(f))
 return {k:np.array([float(r[k]) for r in rs]) for k in ['time_s','x','actual_jerk']}
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False,'svg.fonttype':'none'})
fig=plt.figure(figsize=(13,11),layout='constrained');gs=fig.add_gridspec(3,2,height_ratios=[1,1,.9]);ax1=fig.add_subplot(gs[0,0]);ax2=fig.add_subplot(gs[0,1]);ax3=fig.add_subplot(gs[1,0]);ax4=fig.add_subplot(gs[1,1]);ax5=fig.add_subplot(gs[2,0]);ax6=fig.add_subplot(gs[2,1])
for case,apos,ajerk in [('return_generous',ax1,ax2),('return_tight',ax3,ax4)]:
 for method in METHODS:
  d=trace(case,method);apos.plot(d['time_s'],1000*d['x'],label=NAMES[method],color=COLORS[method],lw=1.8);ajerk.plot(d['time_s'],d['actual_jerk'],color=COLORS[method],lw=1.4)
 for ax in [apos,ajerk]:
  ax.axvspan(0,.52,color='#e4e9ed',alpha=.65,zorder=-2);ax.axvline(.52,color='#65727d',lw=1,ls=':');ax.set_xlim(.15,1.8);ax.set_xlabel('Time (s)');ax.grid(alpha=.2)
 apos.axhspan(-.2,.2,color='#b3dce8',alpha=.8,zorder=-1);apos.set_ylabel('Actual position (mm)');ajerk.set_ylabel('Actual jerk (m/s³)')
 deadline=1.7 if case=='return_generous' else 1.3
 for ax in [apos,ajerk]:ax.axvline(deadline,color='black',ls='--',lw=1)
ax1.set_title('1.70 s deadline: all three methods pass');ax2.set_title('Same initial state; native matched arrival = FIR arrival')
ax3.set_title('1.30 s deadline: only native fast passes');ax4.set_title('Rejected FIR revision continues to the old target')
ax1.legend(loc='upper right',frameon=False)
generous={r['method']:r for r in summary if r['case']=='return_generous'}
for ax,field,scale,title,ylabel in [(ax5,'suffix_until_horizon_jerk_energy_m2_s5',1.,'Lower integral of squared jerk','Integral j² dt (m²/s⁵)'),(ax6,'suffix_until_horizon_extra_forward_excursion_m',1000.,'But greater forward excursion after revision','Extra forward excursion (mm)')]:
 lows=np.array([generous[m][field+'_min'] for m in METHODS])*scale;highs=np.array([generous[m][field+'_max'] for m in METHODS])*scale;mids=(lows+highs)/2
 ax.bar(range(3),mids,color=[COLORS[m] for m in METHODS],width=.6,alpha=.85);ax.errorbar(range(3),mids,yerr=np.array([mids-lows,highs-mids]),fmt='none',ecolor='black',capsize=5)
 ax.set_xticks(range(3),[NAMES[m] for m in METHODS]);ax.set_ylabel(ylabel);ax.set_title(title);ax.grid(axis='y',alpha=.2)
 for i,(lo,hi) in enumerate(zip(lows,highs)):ax.text(i,hi+.02*max(highs),f'{lo:.2f}–{hi:.2f}',ha='center',va='bottom',fontsize=10)
 ax.set_ylim(0,max(highs)*1.18)
fig.set_layout_engine('constrained', rect=(0, .08, 1, .9))
fig.suptitle('Equal starting motion exposes a real tradeoff',fontsize=19,fontweight='bold',y=.995)
fig.text(.5,.015,'Numerical scalar model. Curves: r = 100/s, w = 0.01 m/s². Bars: all six constant plant cases.\nGray = shared prefix. Dashed black = deadline. Squared jerk is a smoothness proxy, not physical energy.\nFIR waits 0.10 s. Native matched uses minimum_duration = 0.90 s, not a minimum-jerk objective.',ha='center',fontsize=10)
fig.savefig(HERE/'common-prefix-comparison.png',dpi=150,bbox_inches='tight');fig.savefig(HERE/'common-prefix-comparison.svg',bbox_inches='tight');plt.close(fig)
(HERE/'figure-inputs.json').write_text(json.dumps({'trace_files':inputhash,'summary_sha256':hashlib.sha256((HERE/'comparison-summary.json').read_bytes()).hexdigest(),'selected_curve':'central declared rate 100/s and nonzero declared disturbance 0.01 m/s²; ranges cover all six cases'},indent=2)+'\n')
