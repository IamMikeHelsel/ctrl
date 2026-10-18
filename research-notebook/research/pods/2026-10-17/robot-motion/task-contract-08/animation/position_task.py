"""Conditional reference/tube explanation. No simulated physical path is drawn."""
from manim import *

BG = '#101820'
INK = '#EDF4F5'
MUTED = '#A7B7BC'
TEAL = '#68C9D2'
GREEN = '#8FDCAB'
RED = '#F49075'

def label(s, size=24, color=INK):
    return Text(s, font='Noto Sans', font_size=size, color=color)

def reference_mm(t):
    z = (t - .22) / .2
    if z <= 0: return 0.
    if z >= 4: return 20.
    return 20 * sum(c * max(z-k, 0.)**4 for k,c in enumerate([1,-4,6,-4,1])) / 24

class PositionTask(Scene):
    def construct(self):
        self.camera.background_color = BG
        title = label('A tracking bound can support a task deadline.', 34).to_edge(UP, buff=.4)
        intro = VGroup(label('Old goal: 0 mm. New authoritative goal: 20 mm.', 27),
            label('Issue at 0.20 s. Execute at 0.22 s.', 25, TEAL),
            label('One scalar model. Conditional theorem. No robot measurement.', 20, MUTED)).arrange(DOWN, buff=.35)
        self.play(FadeIn(title), FadeIn(intro), run_time=.7)
        self.wait(2.3)
        self.play(FadeOut(intro), run_time=.4)
        subtitle = label('Reference q in blue. Proved bound q ± 0.2 mm in green.', 21, MUTED).next_to(title, DOWN, buff=.2)
        axes = Axes(x_range=[0,2,.5], y_range=[0,22,10], x_length=10.6,
            y_length=3.4, tips=False, axis_config={'color':MUTED,'stroke_width':1.4}).move_to(DOWN*.1)
        ts = np.linspace(0,2,401)
        band = Polygon(*[axes.c2p(t,reference_mm(t)+.2) for t in ts],
            *[axes.c2p(t,reference_mm(t)-.2) for t in ts[::-1]],
            fill_color=GREEN,fill_opacity=.65,stroke_width=0)
        curve = VMobject(color=TEAL,stroke_width=2.2).set_points_as_corners([axes.c2p(t,reference_mm(t)) for t in ts])
        ticks = VGroup(*[label(str(y),17,MUTED).next_to(axes.c2p(0,y),LEFT,buff=.12) for y in [0,10,20]],
            *[label(str(t),16,MUTED).next_to(axes.c2p(t,0),DOWN,buff=.13) for t in [0,.22,.62,1.02,1.5,2]])
        units = VGroup(label('mm',16,MUTED).next_to(axes.c2p(0,22),LEFT,buff=.15),
            label('Absolute time (s)',17,MUTED).move_to(DOWN*2.48))
        goal = DashedLine(axes.c2p(0,20),axes.c2p(2,20),color=MUTED,stroke_width=1)
        footer = label('The band bounds physical position x. It is not a predicted x path.',20,MUTED).to_edge(DOWN,buff=.37)
        clock=ValueTracker(0)
        probe=always_redraw(lambda:VGroup(Line(axes.c2p(clock.get_value(),0),axes.c2p(clock.get_value(),22),color=INK,stroke_opacity=.3),Dot(axes.c2p(clock.get_value(),reference_mm(clock.get_value())),radius=.045,color=TEAL)))
        self.play(FadeIn(subtitle),Create(axes),FadeIn(ticks),FadeIn(units),Create(goal),FadeIn(band),Create(curve),FadeIn(footer),run_time=1)
        self.add(probe)
        self.play(clock.animate.set_value(.62),run_time=4,rate_func=linear)
        midpoint=label('At 0.62 s: 9.8 ≤ x ≤ 10.2 mm. Progress from the old goal ≥ 9.8 mm.',21,GREEN).move_to(DOWN*3.0)
        self.play(Transform(footer,midpoint),run_time=.4);self.wait(2.6)
        self.play(clock.animate.set_value(1.02),run_time=2.3,rate_func=linear)
        arrival=label('From 1.02 through 2.00 s: position stays within 0.2 mm of the goal.',22,GREEN).move_to(DOWN*3.0)
        self.play(Transform(footer,arrival),run_time=.4)
        deadline=DashedLine(axes.c2p(1.5,0),axes.c2p(1.5,22),color=GREEN,stroke_width=1.5)
        deadline_label=label('Deadline 1.5 s',18,GREEN).next_to(axes.c2p(1.5,14),RIGHT,buff=.15)
        self.play(Create(deadline),FadeIn(deadline_label),clock.animate.set_value(2),run_time=3,rate_func=linear)
        self.wait(1.5)
        bad=label('A 0.62 s arrival deadline fails: at least 9.8 mm still remains.',23,RED).move_to(DOWN*3.0)
        self.play(Transform(footer,bad),clock.animate.set_value(.62),run_time=.4);self.wait(2.1)
        probe.clear_updaters()
        self.play(*[FadeOut(m) for m in list(self.mobjects)],run_time=.5)
        end=VGroup(label('Position arrival is proved. Physical rest is still open.',31,GREEN),
            label('Assumptions: the specified continuous-state controller and scalar lag model;',20,MUTED),
            label('response rate 80–120 /s; disturbance magnitude ≤ 0.01 m/s²;',20,MUTED),
            label('the stated initial transformed-error cube; no later goal change through 2 s.',20,MUTED),
            label('The moving-reversal comparison is a separate result.',22,RED)).arrange(DOWN,buff=.3)
        self.play(FadeIn(end),run_time=.5);self.wait(4)
