"""Explain the checked scalar command contract; this is not a robot simulation."""
from manim import *
BG='#101820';INK='#EDF4F5';MUTED='#A7B7BC';GREEN='#8FDCAB';TEAL='#68C9D2';RED='#F49075'
def txt(s,size=25,color=INK):return Text(s,font='Noto Sans',font_size=size,color=color)

class SmoothReplanning(Scene):
 def construct(self):
  self.camera.background_color=BG
  scope=txt('Illustrative scalar command. No physical robot test.',17,MUTED).to_edge(DOWN,buff=.22)
  title=txt('Think often. Switch smoothly.',39).to_edge(UP,buff=.5)
  intro=VGroup(txt('New plans can arrive at any time.',29),
    txt('The executed motion still needs a safe join.',28,TEAL),
    txt('Check position, velocity and acceleration at the switch.',23,MUTED)).arrange(DOWN,buff=.38)
  self.play(FadeIn(title),FadeIn(intro),FadeIn(scope),run_time=1);self.wait(2)
  self.play(FadeOut(title),FadeOut(intro),run_time=.5)

  title=txt('A wait does not make a switch smooth.',34).to_edge(UP,buff=.4)
  subtitle=txt('Each segment has jerk magnitude 10 m/s³. The join still matters.',20,MUTED).next_to(title,DOWN,buff=.18)
  axes=Axes(x_range=[0,40,10],y_range=[-.25,.30,.1],x_length=10.2,y_length=3.6,
    tips=False,axis_config={'color':MUTED,'stroke_width':1.2}).move_to(DOWN*.05)
  labels=VGroup(*[txt(f'{x}',16,MUTED).next_to(axes.c2p(x,-.25),DOWN,buff=.12)for x in [0,10,20,30,40]],
    *[txt(f'{y:g}',16,MUTED).next_to(axes.c2p(0,y),LEFT,buff=.14)for y in [-.2,0,.2]])
  ylabel=txt('Acceleration (m/s²)',17,MUTED).next_to(axes,LEFT,buff=.25).rotate(PI/2)
  xlabel=txt('Time (ms)',17,MUTED).move_to(DOWN*2.5)
  switch=DashedLine(axes.c2p(20,-.25),axes.c2p(20,.27),color=MUTED,stroke_width=1.4)
  switchlabel=txt('Switch at 20 ms',18,MUTED).next_to(axes.c2p(20,.28),UP,buff=.12)
  matched=VMobject(color=GREEN,stroke_width=4).set_points_as_corners([
    axes.c2p(0,0),axes.c2p(20,.2),axes.c2p(40,0)])
  raw=VMobject(color=RED,stroke_width=3.4).set_points_as_corners([
    axes.c2p(20,-.2),axes.c2p(40,0)])
  jump=DashedLine(axes.c2p(20,.2),axes.c2p(20,-.2),color=RED,stroke_width=3.5,dash_length=.08)
  legend=VGroup(txt('Matched replacement',19,GREEN),txt('Raw acceleration reset',19,RED)).arrange(RIGHT,buff=.65).move_to(DOWN*2.98)
  self.play(FadeIn(title),FadeIn(subtitle),Create(axes),FadeIn(labels),FadeIn(ylabel),
    FadeIn(xlabel),Create(switch),FadeIn(switchlabel),FadeIn(legend),run_time=1)
  self.play(Create(matched,rate_func=linear),Create(raw,rate_func=linear),run_time=5)
  badge=txt('Jump: 0.4 m/s²',20,RED).move_to(axes.c2p(32,.245))
  self.play(Create(jump),FadeIn(badge),run_time=.5);self.wait(2.5)
  self.play(*[FadeOut(m)for m in list(self.mobjects)if m is not scope],run_time=.5)

  title=txt('Same start. Same duration. Same limits.',34).to_edge(UP,buff=.5)
  start=txt('q = 0   |   v = 0.1 m/s   |   a = 0   |   duration = 20 ms',22,MUTED).next_to(title,DOWN,buff=.3)
  kind=txt('One constant-jerk segment per candidate',19,MUTED).move_to(UP*2.05)
  limit=txt('Jerk limit: 10 m/s³',30,TEAL).move_to(UP*1.45)
  rows=VGroup(
    VGroup(txt('ACCEPT',25,GREEN),txt('2.0133… mm target',25),txt('jerk 10',25,GREEN)).arrange(RIGHT,buff=.65),
    VGroup(txt('REJECT',25,RED),txt('2.5000 mm target',25),txt('jerk 375',25,RED)).arrange(RIGHT,buff=.65)
  ).arrange(DOWN,buff=.65).move_to(DOWN*.05)
  other=txt('Also checked: position ±10 mm  |  |v| ≤0.2 m/s  |  |a| ≤1 m/s²',19,MUTED).move_to(DOWN*1.65)
  caption=txt('A nearby target can still demand an abrupt motion.',25,TEAL).move_to(DOWN*2.5)
  self.play(FadeIn(title),FadeIn(start),FadeIn(kind),FadeIn(limit),FadeIn(rows),FadeIn(other),FadeIn(caption),run_time=1);self.wait(6)
  self.play(*[FadeOut(m)for m in list(self.mobjects)if m is not scope],run_time=.5)

  title=txt('What the proof gives us',36).to_edge(UP,buff=.5)
  body=VGroup(txt('24 Lean theorem statements checked.',28,TEAL),
    txt('Matching state preserves a smooth join.',27,GREEN),
    txt('Finite admitted replacements preserve the jerk bound.',25),
    txt('A minimum wait alone cannot provide that bound.',24,RED)).arrange(DOWN,buff=.36).move_to(UP*.25)
  limits=VGroup(txt('Bounded jerk can still allow dithering.',23,MUTED),
    txt('Physical tracking and task progress need separate checks.',22,MUTED),
    txt('Known trajectory mathematics; no new-method claim.',18,MUTED)).arrange(DOWN,buff=.18).move_to(DOWN*2.35)
  self.play(FadeIn(title),FadeIn(body),FadeIn(limits),run_time=1);self.wait(5)
