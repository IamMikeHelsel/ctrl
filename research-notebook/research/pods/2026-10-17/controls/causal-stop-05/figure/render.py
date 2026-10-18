#!/usr/bin/env python3
"""Render the independently reviewed fixed comparison as a local HTML plot."""
from pathlib import Path
import csv
import hashlib
import json
import plotly.graph_objects as go
from plotly.subplots import make_subplots

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent/'builder'
data = json.loads((SOURCE/'result.json').read_text())
fig = make_subplots(rows=4, cols=1, shared_xaxes=True, vertical_spacing=.075,
                    subplot_titles=['Position error against the same reference',
                                    'Actual axis jerk', 'Acceleration command',
                                    'Actual velocity near the endpoint'])
styles = [('Direct', '#126782'), ('Original filter', '#c34b38'),
          ('Compensated filter', '#95720b')]
for case, (name, color) in zip(data['cases'], styles):
    with (SOURCE/case['trace']).open() as f:
        rows = list(csv.DictReader(f))
    t = [float(r['t']) for r in rows]
    for index, field, factor, unit in [(1, 'ex', 1000, 'mm'),
                                     (2, 'actual_jerk', 1, 'm/s³'),
                                     (3, 'u', 1, 'm/s²'),
                                     (4, 'v', 1000, 'mm/s')]:
        fig.add_trace(go.Scatter(x=t, y=[float(r[field])*factor for r in rows],
                                name=name, legendgroup=name, showlegend=index == 1,
                                line=dict(color=color, width=2),
                                hovertemplate='%{x:.5f} s<br>%{y:.6f} '+unit+'<extra>'+name+'</extra>'),
                      row=index, col=1)
fig.add_hrect(y0=-.2, y1=.2, fillcolor='#126782', opacity=.08, line_width=0, row=1, col=1)
for y in [-.2, .2]:
    fig.add_hline(y=y, line=dict(color='#126782', width=1, dash='dash'), row=1, col=1)
for row in range(1, 5):
    fig.add_vline(x=.255, line=dict(color='#777', width=1, dash='dot'), row=row, col=1)
    fig.add_vline(x=10491307/7508900, line=dict(color='#777', width=1, dash='dot'), row=row, col=1)
fig.update_xaxes(title_text='Time (s)', row=4, col=1)
fig.update_xaxes(title_text='Time (s)', showticklabels=True, row=3, col=1)
for row, unit in [(1, 'mm'), (2, 'm/s³'), (3, 'm/s²'), (4, 'mm/s')]:
    fig.update_yaxes(title_text=unit, row=row, col=1)
fig.update_xaxes(range=[0, 1.5], matches=None)
fig.update_xaxes(matches='x', row=2, col=1)
fig.update_xaxes(matches='x', row=3, col=1)
fig.update_xaxes(range=[1.25, 1.5], row=4, col=1, matches=None)
fig.update_layout(template='plotly_white', height=1100,
                  margin=dict(l=65, r=25, t=70, b=55),
                  font=dict(family='system-ui, sans-serif', size=13),
                  legend=dict(orientation='h', y=1.065, x=0),
                  hovermode='x unified')
plot = fig.to_html(full_html=False, include_plotlyjs=True,
                   config={'displaylogo': False, 'responsive': True})
assert len(fig.data) == 12
assert all(len(trace.x) == 3010 and len(trace.y) == 3010 for trace in fig.data)
assert tuple(fig.layout.xaxis.range) == (0, 1.5)
assert tuple(fig.layout.xaxis4.range) == (1.25, 1.5)
assert fig.layout.xaxis4.matches is None
table = ''.join('<tr><td>'+name+'</td><td>'+format(c['peaks']['ex']['max_abs']*1000,'.4f')+
                '</td><td>'+format(c['peaks']['actual_jerk']['max_abs'],'.3f')+
                '</td><td>'+format(c['sampled_command_total_variation'],'.3f')+'</td></tr>'
                for c, (name, _) in zip(data['cases'], styles))
html = '''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>A filter can make motion worse — fixed comparison</title>
<style>body{font:17px/1.5 system-ui,sans-serif;color:#18303d;max-width:1100px;margin:36px auto;padding:0 24px;background:#fafcfb}h1{font-size:32px;line-height:1.2}p{max-width:900px}table{border-collapse:collapse;width:100%;margin:25px 0}th,td{padding:10px;border-bottom:1px solid #ced8dc;text-align:right}th:first-child,td:first-child{text-align:left}.note{border-left:4px solid #126782;padding:10px 18px;background:#edf4f6}a{color:#126782}</style>
<h1>A filter can make motion worse</h1>
<p>On this fixed motion, the direct controller has lower position error, actual jerk, and command variation than either slow filter. This result is specific to the declared model and initial states.</p>
<p class="note"><strong>Independent numerical review passed.</strong> The reviewer checked all 9,030 saved rows with 80-digit arithmetic. Sampled violations reject the 0.2 mm tracking target for both filters. The plots show numerical values.</p>
<p class="note"><strong>The direct controller now has a separate all-time proof.</strong> An independently reviewed Lean theorem proves position error at most 0.2 mm throughout this same 1.5 s reference, for every supplied trajectory that meets the stated model assumptions. It covers actuator rates from 80 to 120/s and disturbances up to 0.01 m/s² in magnitude. This is a conditional model theorem, not a proof of physical stopping or hardware behavior. <a href="../../direct-reference-06/grader/review-report.txt">Read the proof review.</a></p>
<table><thead><tr><th>Controller</th><th>Peak error (mm)</th><th>Peak actual jerk (m/s³)</th><th>Command variation (m/s²)</th></tr></thead><tbody>'''+table+'''</tbody></table>
<p>The blue band marks the ±0.2 mm position target. Dotted lines mark execution of the new reference at 0.255 s and its arrival at the endpoint at about 1.397 s. The last panel zooms into the final quarter second. Click a legend entry to hide or show a controller. Drag to zoom; double-click to reset.</p>
'''+plot+'''
<p>All three runs share the same plant initial state, reference, 1.5 s deadline, actuator rate of 80/s, and disturbance of 0.01 m/s². Filter states are retained from zero. The algebraic direct command starts at 5/48 m/s². No state is reset. Command variation is a sampled approximation. Actual jerk, reference jerk, and command derivative are different quantities.</p>
<p>All endpoint position errors are below 0.2 mm, but the actual axes still have residual velocity or acceleration. No physical stop or exact travel-corridor acceptance is claimed. There is no hardware evidence.</p>
<p>The timestamps in these runs are aligned. Adding the command filter changes the feedback-loop dynamics. For this fixed rate and filter, the resulting model has a lightly damped mode at about 4.92 Hz. Changing the feedforward coefficient does not remove that mode. This is different from applying a command to a stale observation. <a href="../../timing-diagnosis-07/result.json">Read the symbolic calculation and numerical roots.</a></p>
<p><a href="../grader/grade.txt">Independent grade and limits</a> · <a href="../builder/report.txt">Model and methods</a> · <a href="../builder/result.json">Full numerical results</a></p>
</html>'''
(HERE/'index.html').write_text(html)
(HERE/'provenance.json').write_text(json.dumps({
    'source_results_sha256': hashlib.sha256((SOURCE/'result.json').read_bytes()).hexdigest(),
    'independent_grade_sha256': hashlib.sha256((HERE.parent/'grader/grade.txt').read_bytes()).hexdigest(),
    'direct_proof_review_sha256': hashlib.sha256((HERE.parents[1]/'direct-reference-06/grader/review-report.txt').read_bytes()).hexdigest(),
    'renderer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'html_sha256': hashlib.sha256((HERE/'index.html').read_bytes()).hexdigest(),
    'plot_configuration_checks': '12 traces, 3010 rows each; first three panels0..1.5s, last panel1.25..1.5s; last panel is not range-linked.',
    'visual_browser_check': 'Automated check blocked by file: URL policy; no workaround attempted. A user-supplied screenshot confirms the prior version title, table and upper plots. The added proof and dynamics notes have not been visually checked. Plot data are unchanged. Last panel was not shown in the screenshot.',
    'data': 'All saved trace rows; no resampling or smoothing; plot is numerical evidence only.'
}, indent=2)+'\n')
print(HERE/'index.html')
