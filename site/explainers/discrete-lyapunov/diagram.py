"""Write diagram.svg: V's level sets, the unit circle, and the first steps of a trajectory.

    uv run --no-project --with numpy site/explainers/discrete-lyapunov/diagram.py

Colors come from CSS classes in ../explainer.css, so the SVG follows the page theme.
"""

from pathlib import Path

import numpy as np
from example import V, level_set, trajectory

W, H = 720, 430
CX, CY, S = 250, 215, 165  # origin and px per unit


def pt(x):
    return CX + S * x[0], CY - S * x[1]


def poly(points, cls):
    d = " ".join(f"{a:.1f},{b:.1f}" for a, b in map(pt, points))
    return f'<polyline class="{cls}" points="{d} {d.split()[0]}"/>'


xs = trajectory(steps=7)
parts = [
    f'<svg class="diagram" viewBox="0 0 {W} {H}" role="img" '
    'aria-labelledby="dl-title dl-desc" xmlns="http://www.w3.org/2000/svg">',
    '<title id="dl-title">Level sets of V and a trajectory</title>',
    '<desc id="dl-desc">Each step of x_{k+1} = A x_k lands on a smaller ellipse of '
    "V(x) = x transpose P x. The first step leaves the dashed unit circle, so the "
    "Euclidean norm grew, yet V still fell.</desc>",
    f'<line class="axis" x1="{CX - 200}" y1="{CY}" x2="{CX + 200}" y2="{CY}"/>',
    f'<line class="axis" x1="{CX}" y1="{CY - 200}" x2="{CX}" y2="{CY + 200}"/>',
]
t = np.linspace(0, 2 * np.pi, 240)
parts.append(poly(np.stack([np.cos(t), np.sin(t)]).T, "euclid"))
for k, x in enumerate(xs):
    parts.append(poly(level_set(V(x)), "level strong" if k == 0 else "level"))
d = " ".join(f"{a:.1f},{b:.1f}" for a, b in map(pt, xs))
parts.append(f'<polyline class="path" points="{d}"/>')
for k, x in enumerate(xs):
    a, b = pt(x)
    cls = "pt start" if k == 0 else ("pt warn" if k == 1 else "pt")
    parts.append(f'<circle class="{cls}" cx="{a:.1f}" cy="{b:.1f}" r="{5 if k < 2 else 3.6}"/>')
    if k < 3:
        dx, dy = (10, -10) if k != 1 else (12, 16)
        parts.append(
            f'<text x="{a + dx:.1f}" y="{b + dy:.1f}" font-size="15">x<tspan font-size="11" '
            f'dy="4">{k}</tspan></text>'
        )

# Legend on the right.
lx, ly = 470, 120
legend = [
    ("level strong", "solid", "Level set  V(x) = V(x₀)"),
    ("level", "solid", "Level sets through x₁, x₂, …"),
    ("euclid", "dash", "Unit circle  ‖x‖ = 1"),
]
for i, (cls, _, text) in enumerate(legend):
    y = ly + i * 30
    parts.append(f'<line class="{cls}" x1="{lx}" y1="{y}" x2="{lx + 30}" y2="{y}"/>')
    parts.append(f'<text x="{lx + 40}" y="{y + 5}" font-size="14">{text}</text>')
notes = [
    "x₁ is outside the unit circle:",
    "the plain norm went up.",
    "",
    "x₁ is inside V's level set:",
    "the energy V still went down.",
]
for i, line in enumerate(notes):
    parts.append(
        f'<text class="muted-text" x="{lx}" y="{ly + 120 + i * 21}" font-size="14">{line}</text>'
    )
parts.append("</svg>")
Path(__file__).with_name("diagram.svg").write_text("\n".join(parts) + "\n")
print("wrote diagram.svg")
