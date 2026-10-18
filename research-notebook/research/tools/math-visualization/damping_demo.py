"""Generate a self-contained Plotly teaching example; no service or account."""
from pathlib import Path
import json
import platform
import numpy as np
import scipy
from scipy.signal import step
import plotly
import plotly.graph_objects as go

OUT = Path(__file__).resolve().parent
t = np.linspace(0, 5, 1001)
omega = 6.0
zetas = [0.05, 0.2, 0.4, 0.7, 1.0, 1.5]
fig = go.Figure()
errors = {}
for i, zeta in enumerate(zetas):
    _, y = step(([omega**2], [1, 2*zeta*omega, omega**2]), T=t)
    if zeta < 1:
        d = np.sqrt(1-zeta*zeta)
        exact = 1-np.exp(-zeta*omega*t)*(np.cos(omega*d*t)+zeta/d*np.sin(omega*d*t))
    elif zeta == 1:
        exact = 1-(1+omega*t)*np.exp(-omega*t)
    else:
        p = -omega*(zeta-np.sqrt(zeta*zeta-1))
        q = -omega*(zeta+np.sqrt(zeta*zeta-1))
        exact = 1+(q*np.exp(p*t)-p*np.exp(q*t))/(p-q)
    error = float(np.max(np.abs(exact-y)))
    assert error < 1e-10, (zeta, error)
    assert y[0] == 0 and np.all(np.isfinite(y))
    errors[str(zeta)] = error
    fig.add_trace(go.Scatter(x=t.tolist(), y=y.tolist(), name=f'Damping {zeta:g}',
                            visible=i == 3, line=dict(color='#087f8c', width=3)))
fig.add_hline(y=1, line_dash='dash', line_color='#6c7581', annotation_text='Target')
fig.update_layout(
    template='plotly_white', height=530, font=dict(family='Arial', size=15, color='#203038'),
    margin=dict(l=65, r=30, t=25, b=130), showlegend=False,
    xaxis=dict(title='Time (s)', range=[0, 5]),
    yaxis=dict(title='Response (normalized)', range=[0, 2]),
    sliders=[dict(active=3, currentvalue=dict(prefix='Damping ratio: '), pad=dict(t=55),
                  steps=[dict(label=str(z), method='update',
                              args=[{'visible': [i == j for j in range(len(zetas))]}])
                         for i, z in enumerate(zetas)])])
chart = fig.to_html(full_html=False, include_plotlyjs=True,
                    config={'displaylogo': False, 'responsive': True}, div_id='damping-demo')
html = '''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>See what damping does</title><style>
body{margin:0;background:#f6f5ef;color:#203038;font:17px/1.6 system-ui,sans-serif}
main{max-width:1000px;margin:auto;padding:38px 24px}h1{font:44px/1.15 Georgia,serif}
p{max-width:800px}.formula{font:22px Georgia,serif;background:white;padding:18px;border-left:4px solid #087f8c}
.note{font-size:14px;color:#53616b}a{color:#087f8c}</style><main>
<h1>See what damping does.</h1><p>Move the slider. Low damping lets the response ring.
At a damping ratio of 1, this model approaches the target without overshoot.
More damping slows its approach.</p>
<p class="formula">y″ + 2ζω y′ + ω²y = ω², &nbsp; y(0) = y′(0) = 0</p>
<p>The target steps from 0 to 1 at time zero. The natural frequency ω stays at
6 rad/s. The slider changes ζ, the damping ratio.</p>'''+chart+'''
<p class="note">Teaching example for an ideal second-order model. This is not our
robot model or evidence for its controller. Numerical values match the closed-form
step response to the tolerance recorded in verification.json. Hover for values,
drag to zoom, double-click to reset, or use the camera to save a PNG.</p>
<p><a href="guide.txt">Open-source tools guide</a> ·
<a href="damping_demo.py">Editable source</a></p></main></html>'''
(OUT/'damping-demo.html').write_text(html)
result = {'python': platform.python_version(), 'numpy': np.__version__,
          'scipy': scipy.__version__, 'plotly': plotly.__version__,
          'cases': len(zetas), 'samples_per_case': len(t),
          'closed_form_max_abs_errors': errors,
          'numeric_check_passed': True, 'browser_interaction_tested': False,
          'html_uses_embedded_plotly': True}
(OUT/'verification.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
