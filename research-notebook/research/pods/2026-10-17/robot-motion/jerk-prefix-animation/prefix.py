"""Manim explanation of one checked ideal reference prefix, not the physical axis."""
from pathlib import Path
from fractions import Fraction
import json
import numpy as np
from manim import *

BG = '#101c29'
INK = '#edf3f5'
MUTED = '#a9b9c7'
COLORS = ['#f6c777', '#57d0c5', '#83b9f4', '#e7a5e8']
DATA = json.loads(Path(__file__).with_name('exact-check.json').read_text())
SEGMENTS = [{k: float(Fraction(v)) for k,v in s.items()} for s in DATA['segments']]

def label(s, size=22, color=INK):
    return Text(s, font='Noto Sans', font_size=size, color=color)

def state(ms):
    """Return reference jerk, acceleration, velocity in mm/s, position in mm."""
    t = min(max(ms/1000, 0), .12)
    k = min(int((t+1e-14)/.02), 5)
    p = SEGMENTS[k]
    dt = min(max(t-p['start_elapsed_s'], 0), .02)
    j, a, v, q = p['jerk_m_s3'], p['a0_m_s2'], p['v0_m_s'], p['q0_m']
    return j, a+j*dt, (v+a*dt+j*dt**2/2)*1000, (q+v*dt+a*dt**2/2+j*dt**3/6)*1000

class JerkPrefix(Scene):
    def construct(self):
        self.camera.background_color = BG
        title = label('Alternating jerk can still build speed.', 34).to_edge(UP, buff=.25)
        subtitle = label('Jerk is the rate of change of acceleration.', 23, MUTED).next_to(title, DOWN, buff=.15)
        scope = label('One ideal reference prefix • execution begins at 0.22 s • q is reference position, not physical x', 16, MUTED).to_edge(DOWN, buff=.16)
        self.add(title, subtitle, scope)

        rows = [2.0, .7, -.6, -1.9]
        ranges = [(-9, 9, 7.5), (-.02, .18, .15), (-.6, 10.2, 3), (-.04, .6, .2)]
        names = [('Jerk', 'm/s³'), ('Acceleration', 'm/s²'), ('Velocity', 'mm/s'), ('Position q', 'mm')]
        axes, curves = [], []
        for i, (cy, yr, name) in enumerate(zip(rows, ranges, names)):
            ax = Axes(x_range=[0,120,20], y_range=list(yr), x_length=9.5, y_length=1.0,
                      tips=False, axis_config={'stroke_color': MUTED, 'stroke_width': 1.0,
                                               'include_ticks': False}).move_to(RIGHT*.8+UP*cy)
            axes.append(ax)
            self.add(ax)
            self.add(label(name[0], 21, COLORS[i]).move_to(LEFT*5.75+UP*(cy+.23)))
            self.add(label(name[1], 16, MUTED).move_to(LEFT*5.75+UP*(cy-.08)))
            for tick in range(0, 121, 20):
                self.add(DashedLine(ax.c2p(tick, yr[0]), ax.c2p(tick, yr[1]),
                                    color=MUTED, stroke_opacity=.22, stroke_width=.8))
            if i == 0:
                points=[]
                for k in range(6):
                    j = 7.5*(-1 if k % 2 else 1)
                    points.extend([ax.c2p(k*20, j), ax.c2p((k+1)*20, j)])
            else:
                points=[ax.c2p(ms, state(ms)[i]) for ms in np.linspace(0,120,481)]
            curve=VMobject(color=COLORS[i], stroke_width=3).set_points_as_corners(points)
            curves.append(curve)
            self.add(curve)
            # Explicit scale labels avoid an unexplained normalized vertical axis.
            scale_ticks = [[-7.5,0,7.5],[0,.15],[0,3,6,9],[0,.2,.4,.54]][i]
            for val in scale_ticks:
                self.add(label(f'{val:g}', 14, MUTED).next_to(ax.c2p(0,val), LEFT, buff=.08))

        for ms in range(0,121,20):
            self.add(label(str(ms), 16, MUTED).next_to(axes[-1].c2p(ms, ranges[-1][0]), DOWN, buff=.12))
        self.add(label('Elapsed execution time (ms)', 18, MUTED).move_to(DOWN*2.86+RIGHT*.8))
        timer=ValueTracker(0)
        for i, ax in enumerate(axes):
            yr=ranges[i]
            marker=always_redraw(lambda ax=ax,yr=yr: Line(ax.c2p(timer.get_value(),yr[0]),ax.c2p(timer.get_value(),yr[1]),color=INK,stroke_width=1.5))
            dot=always_redraw(lambda ax=ax,i=i: Dot(ax.c2p(timer.get_value(),state(timer.get_value())[i]),radius=.055,color=COLORS[i]))
            self.add(marker,dot)
        note=label('Start at rest: q = 0, v = 0, a = 0.', 22, INK).move_to(DOWN*3.3)
        self.add(note)
        self.wait(1.2)
        def set_note(message, size=22, color=INK):
            nonlocal note
            self.remove(note)
            note=label(message,size,color).move_to(DOWN*3.3)
            self.add(note)
        # The time marker traverses the complete prefix at one constant display speed.
        set_note('Positive jerk raises acceleration to +0.15 m/s².',color=COLORS[1])
        self.play(timer.animate.set_value(20),run_time=2,rate_func=linear)
        set_note('Negative jerk returns acceleration to zero. Velocity still rises.',21,COLORS[2])
        self.play(timer.animate.set_value(40),run_time=2,rate_func=linear)
        set_note('Acceleration stays nonnegative. Each pair adds velocity.',color=COLORS[2])
        self.play(timer.animate.set_value(120),run_time=8,rate_func=linear)
        set_note('At 120 ms: q = 0.54 mm, v = 9 mm/s, a = 0. This is not rest.')
        self.remove(subtitle)
        self.add(label('Bounded jerk does not, by itself, keep a stationary task still.',23,MUTED).next_to(title,DOWN,buff=.15))
        self.wait(4)
