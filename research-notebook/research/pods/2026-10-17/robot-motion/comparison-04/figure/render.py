"""Present frozen traces; do not simulate, tune, or change any task input."""
import argparse
import csv
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'builder'
METHODS = [('raw', 'Raw target', '#2563a6'),
           ('ruckig', 'Ruckig', '#c34c20'),
           ('fir', 'Four-box reference', '#087f64')]
CASES = [('hold_jitter', 'Hold still while target estimates alternate'),
         ('persistent_goal', 'Move to a lasting new target')]


def read_trace(case, method):
    p = SOURCE / 'traces' / f'{case}__{method}__r80__w01__dt500us.csv.gz'
    with gzip.open(p, 'rt') as f:
        rows = list(csv.DictReader(f))
    # Keep both sides and tiny intervals. Do not interpolate a new trajectory.
    return rows, p


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--static', action='store_true')
    args = parser.parse_args()
    data = {(case, method): read_trace(case, method)
            for case, _ in CASES for method, _, _ in METHODS}
    metrics = list(csv.DictReader((SOURCE / 'metrics.csv').open()))
    selected = [r for r in metrics if r['case'] in dict(CASES)
                and r['rate'] == '80' and r['disturbance'] == '0.01'
                and r['sample_step_s'] == '0.0005']
    assert len(selected) == 6
    if args.static:
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
        fig, axes = plt.subplots(2, 2, figsize=(12, 7), constrained_layout=True)
        for col, (case, title) in enumerate(CASES):
            axes[0, col].set_title(title, loc='left', fontsize=12, weight='bold')
            for method, label, color in METHODS:
                rows, _ = data[case, method]
                t = [float(r['time_s']) for r in rows]
                axes[0, col].plot(t, [1000*float(r['x']) for r in rows],
                                  label=label, color=color, linewidth=1.7)
                axes[1, col].plot(t, [float(r['actual_jerk']) for r in rows],
                                  color=color, linewidth=1.4)
            raw, _ = data[case, 'raw']
            t = [float(r['time_s']) for r in raw]
            axes[0, col].plot(t, [1000*float(r['q']) for r in raw],
                              color='#89929a', linewidth=.7, alpha=.7,
                              label='Delivered target')
            axes[0, col].plot(t, [1000*float(r['truth']) for r in raw],
                              color='#152b38', linewidth=1, linestyle='--',
                              label='Declared task goal')
            if case == 'hold_jitter':
                axes[0, col].axhspan(-.2, .2, color='#087f64', alpha=.09)
            for row in range(2):
                axes[row, col].set_xlim(0, 1.5)
                axes[row, col].grid(alpha=.18)
                axes[row, col].spines[['top','right']].set_visible(False)
            axes[0, col].set_ylabel('Actual position (mm)')
            axes[1, col].set_ylabel('Actual jerk (m/s³)')
            axes[1, col].set_xlabel('Time (s)')
        axes[0, 0].legend(loc='lower right', fontsize=8)
        fig.suptitle('Less motion, more delay — one fixed scalar comparison',
                     fontsize=17, weight='bold')
        fig.text(.5, -.025,
                 'Synthetic scalar model: r = 80/s, w = 0.01 m/s². Sample interval 0.5 ms. '
                 'Display: 0–1.5 s; horizons: hold 2.5 s, step 2.0 s. Review scope in linked report.',
                 ha='center', fontsize=9)
        fig.savefig(HERE / 'comparison.png', dpi=180, bbox_inches='tight')
        return

    import plotly.graph_objects as go
    from plotly.subplots import make_subplots
    figures = []
    for case, title in CASES:
        fig = make_subplots(rows=2, cols=1, shared_xaxes=True,
                            subplot_titles=('Actual position', 'Actual jerk'),
                            vertical_spacing=.12)
        for method, label, color in METHODS:
            rows, _ = data[case, method]
            t = [float(r['time_s']) for r in rows]
            for row, field, scale in [(1,'x',1000), (2,'actual_jerk',1)]:
                fig.add_trace(go.Scatter(x=t, y=[scale*float(r[field]) for r in rows],
                    name=label, legendgroup=method, showlegend=row == 1,
                    line=dict(color=color, width=2)), row=row, col=1)
        rows, _ = data[case, 'raw']
        t = [float(r['time_s']) for r in rows]
        for field, label, dash in [('q','Delivered target','dot'),
                                  ('truth','Declared task goal','dash')]:
            fig.add_trace(go.Scatter(x=t, y=[1000*float(r[field]) for r in rows],
                name=label, line=dict(color='#79838a', width=1, dash=dash)), row=1,col=1)
        if case == 'hold_jitter':
            fig.add_hrect(y0=-.2,y1=.2,fillcolor='#087f64',opacity=.09,
                          line_width=0,row=1,col=1)
        fig.update_layout(template='plotly_white',height=620,
                          margin=dict(l=65,r=20,t=65,b=50),
                          legend=dict(orientation='h',y=1.15),
                          font=dict(family='Arial',size=13))
        fig.update_xaxes(range=[0,1.5])
        fig.update_xaxes(title_text='Time (s)',row=2,col=1)
        fig.update_yaxes(title_text='mm',row=1,col=1)
        fig.update_yaxes(title_text='m/s³',row=2,col=1)
        figures.append('<h2>'+title+'</h2>'+fig.to_html(full_html=False,
            include_plotlyjs=True if not figures else False,
            config={'responsive':True,'displaylogo':False},div_id=case))
    table = ''
    for method, label, _ in METHODS:
        hold = next(r for r in selected if r['method']==method and r['case']=='hold_jitter')
        step = next(r for r in selected if r['method']==method and r['case']=='persistent_goal')
        table += (f'<tr><td>{label}</td><td>{1000*float(hold["hold_peak_m"]):.3f}</td>'
                  f'<td>{float(hold["actual_jerk_peak_m_s3"]):.3f}</td>'
                  f'<td>{float(step["settling_through_horizon_s"]):.4f}</td></tr>')
    review = HERE.parent/'grader/review-report.txt'
    status = ('An independent review is available. Read its scope and findings below.'
              if review.exists() else 'Independent numerical review is in progress.')
    html = '''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Small target changes, real motion</title><style>
body{font:17px/1.6 system-ui,sans-serif;color:#17313d;background:#fafcfc;margin:0}
main{max-width:1080px;margin:auto;padding:28px}h1{font-size:34px;line-height:1.2}
h2{font-size:23px;margin-top:38px}a{color:#165c91}aside{border-left:4px solid #087f64;
padding:12px 18px;background:#edf5f4}table{border-collapse:collapse;width:100%;font-size:15px}
th,td{padding:12px;text-align:left;border-bottom:1px solid #cfdbdf}small{font-size:14px}
</style><main><h1>Small target changes, real motion</h1>
<p>One task is simple: hold still. But the target
estimates keep changing. A fast motion planner follows them. A slower reference
suppresses them. That same slower response costs time when the goal really moves.</p>
<aside>''' + status + ''' These are synthetic inputs and a scalar actuator model.
They are not a full-arm or learned-policy test. The graphs show sampled results.</aside>
<p>All curves use the same physical controller, an actuator rate of 80/s, and
disturbance 0.01 m/s². The four-box width is 0.2 s, with a total tail of 0.8 s.
The green band marks ±0.2 mm about the stationary goal. Click a legend entry to
hide a curve; this helps reveal small jerk values beside the raw controller.</p>
<p><small>The display starts with 0–1.5 s; the hold data run through 2.5 s and the step data through 2.0 s.
Reset the plot axes to see the complete recorded horizon.</small></p>
<table><thead><tr><th>Method</th><th>Hold excursion (mm)</th><th>Hold jerk peak (m/s³)</th>
<th>20 mm move settles at (s)</th></tr></thead><tbody>''' + table + '''</tbody></table>
<p><small>The move is committed at 0.22 s. “Settles” means that position, speed and
acceleration remain inside the stated limits through the fixed observation
horizon. It is not an infinite-time statement. Limits are unchanged between methods.</small></p>
''' + ''.join(figures) + '''<h2>What this comparison does not hide</h2>
<p>The four-box reference takes longer to reach a persistent goal. It also rejects
a separate 50 mm request and misses a separate 400 ms reference deadline. Those
failures remain in the record. An admission guard does not by itself guarantee
that the requested task will finish.</p>
<p>Ruckig is doing the motion-planning job specified by the changing input. The
hold failure here does not show a defect in Ruckig. It shows why an execution
contract must distinguish target estimates from the task that must be achieved.</p>
<p><strong>This noise is especially favorable to the FIR.</strong> It repeats
every 40 ms. The 200 ms averaging window contains exactly five periods. That
gives exact cancellation after the start transient for one box average, and the
four-box cascade inherits it. Irregular noise and equal delay budgets need a
separate comparison before we make a broader claim.</p>
<p><a href="../builder/report.txt">Full experiment report</a> ·
<a href="../builder/metrics.csv">All 72 cases at both resolutions</a> ·
<a href="../grader/review-report.txt">Independent review</a> ·
<a href="../../coordinator/publication-thesis.txt">Claims still to earn</a></p></main></html>'''
    (HERE/'index.html').write_text(html)
    paths = [p for rows,p in data.values()]+[SOURCE/'metrics.csv',SOURCE/'artifact-sha256.json',Path(__file__)]
    (HERE/'provenance.json').write_text(json.dumps({
        'scope':'Presentation of six frozen fine-grid traces; no new simulation.',
        'case_selection':'r=80/s, disturbance=.01, dt=.0005; hold and persistent goal',
        'both_sides_retained':True,'browser_interaction_tested':False,
        'inputs':{str(p.relative_to(HERE.parent.parent)):hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in paths},
        'trace_rows':{case+'__'+method:len(data[case,method][0]) for case,method in data}
    },indent=2)+'\n')
    print('Wrote index.html and provenance.json from six frozen traces.')


if __name__ == '__main__':
    main()
