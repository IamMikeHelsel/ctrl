#!/usr/bin/env python3
"""Render exact source projections; floating conversion is for SVG display only."""
from pathlib import Path
from fractions import Fraction as F
import json
from html import escape
root=Path(__file__).resolve().parent
r=json.loads((root/'results.json').read_text())

def cross(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
def hull(points):
    p=sorted(set(points)); lower=[]; upper=[]
    for a in p:
        while len(lower)>=2 and cross(lower[-2],lower[-1],a)<=0: lower.pop()
        lower.append(a)
    for a in reversed(p):
        while len(upper)>=2 and cross(upper[-2],upper[-1],a)<=0: upper.pop()
        upper.append(a)
    return lower[:-1]+upper[:-1]

svg=['<svg xmlns="http://www.w3.org/2000/svg" width="1080" height="760" viewBox="0 0 1080 760">',
     '<rect width="1080" height="760" fill="#f8fafc"/>',
     '<style>text{font-family:Arial,Helvetica,sans-serif;fill:#172b42}.title{font-size:29px;font-weight:700}.sub{font-size:16px;fill:#4f6276}.label{font-size:15px}.head{font-size:20px;font-weight:700}</style>',
     '<text x="42" y="50" class="title">Which source needs the correction?</text>',
     '<text x="42" y="79" class="sub">Synthetic one-phase model. Exact rational bounds; no vehicle or transient-safety claim.</text>']
for ox,name,title,color in [(60,'baseline','Same-order readings','#db8c3d'),(590,'separated','One separating intervention','#21867a')]:
    svg += [f'<rect x="{ox-20}" y="110" width="470" height="460" rx="15" fill="white" stroke="#d8e1ea"/>',f'<text x="{ox}" y="143" class="head">{title}</text>']
    left=ox+45; top=170; size=300
    def point(p): return left+(float(p[0])+2)*size/4, top+(2-float(p[1]))*size/4
    for i in range(-2,3):
        x,y=point((F(i),F(i)))
        svg += [f'<path d="M{x} {top}V{top+size} M{left} {y}H{left+size}" stroke="#e5eaf0" fill="none"/>',f'<text x="{x}" y="{top+size+22}" text-anchor="middle" class="label">{i}</text>',f'<text x="{left-12}" y="{y+5}" text-anchor="end" class="label">{i}</text>']
    pts=[tuple(map(F,v[:2])) for b in r['stages'][name]['branches'].values() if b['feasible'] for v in b['vertices']]
    poly=' '.join(f'{x:.4f},{y:.4f}' for x,y in map(point,hull(pts)))
    svg += [f'<polygon points="{poly}" fill="{color}" fill-opacity=".28" stroke="{color}" stroke-width="2.5"/>']
    x,y=point((F(1,2),F(1,2)))
    svg += [f'<circle cx="{x}" cy="{y}" r="4" fill="#172b42"/>',f'<text x="{left+150}" y="{top+size+48}" text-anchor="middle" class="label">Wheel contribution w</text>',f'<text x="{left-33}" y="{top-10}" class="label">d</text>']
    wr=r['stages'][name]['ranges']['wheel']
    note='Duplicate + trial mass: same feasible set' if name=='baseline' else 'Shared leakage retained: q = lambda d'
    svg += [f'<text x="{ox}" y="541" class="sub">{escape(note)}</text>']
svg += ['<rect x="40" y="590" width="1000" height="119" rx="14" fill="#172b42"/>',
        '<text x="62" y="620" font-size="18" style="fill:white;font-weight:700">Correction chosen before the experiment: c = -1/2</text>',
        '<text x="62" y="649" font-size="17" style="fill:#dbe6ef">Before: wheel residual can reach 1.60. Decision: not certified.</text>',
        '<text x="62" y="678" font-size="17" style="fill:#aff0d7">After: wheel residual ≤ 4/35 &lt; 1/8; mixed response ≤ 3/5 &lt; 3/4. Accepted.</text>',
        '<text x="42" y="739" class="sub">Shading: all feasible source pairs. Dot: illustrative truth. Naive correction c = -1 is rejected.</text>', '</svg>']
(root/'comparison.svg').write_text('\n'.join(svg)+'\n')
print(root/'comparison.svg')
