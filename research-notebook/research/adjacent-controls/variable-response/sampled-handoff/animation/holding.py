"""Local public explanation: numerical curves, separate conditional theorem."""
from manim import *
from pathlib import Path
import json
from fractions import Fraction
DATA=json.loads((Path(__file__).resolve().parent.parent/'results.json').read_text())
BG='#101820';INK='#EDF4F5';MUTED='#A7B7BC';GREEN='#8FDCAB';TEAL='#68C9D2';RED='#F49075'
def text(s,size=25,color=INK):return Text(s,font='Noto Sans',font_size=size,color=color)

class Holding(Scene):
 def construct(self):
  self.camera.background_color=BG
  title=text('Stopping is only half the job.',37).to_edge(UP,buff=.45)
  intro=VGroup(text('Zero velocity can still leave acceleration.',27),
    text('Releasing the command can let the axis drift.',25,RED),
    text('Check the full state before switching controllers.',25,TEAL)).arrange(DOWN,buff=.35)
  self.play(FadeIn(title),FadeIn(intro),run_time=1);self.wait(3);self.play(FadeOut(intro),run_time=.5)
  subtitle=text('Synthetic axis  |  noisy state reading  |  up to 5 ms command delay',18,MUTED).next_to(title,DOWN,buff=.2)
  axes=Axes(x_range=[0,1.2,.3],y_range=[-.06,.16,.05],x_length=10.1,y_length=3.8,
    tips=False,axis_config={'color':MUTED,'stroke_width':1.4}).move_to(DOWN*.1)
  low,up=[float(Fraction(s))for s in DATA['admission'][0]['tube']]
  zone=Polygon(axes.c2p(0,low),axes.c2p(1.2,low),axes.c2p(1.2,up),axes.c2p(0,up),
    fill_color=GREEN,fill_opacity=.12,stroke_width=0)
  ticks=VGroup(*[text(f'{int(x*100)} cm',15,MUTED).next_to(axes.c2p(0,x),LEFT,buff=.1)for x in [0,.05,.10,.15]],
    *[text(f'{t:g}',15,MUTED).next_to(axes.c2p(t,-.06),DOWN,buff=.1)for t in [0,.3,.6,.9,1.2]])
  walls=VGroup(*[DashedLine(axes.c2p(0,x),axes.c2p(1.2,x),color=RED,stroke_width=1.5)for x in [0,.15]])
  label=text('Seconds after the controller switch',17,MUTED).to_edge(DOWN,buff=.85)
  legends=VGroup(text('Hold: fixed response',18,GREEN),text('Hold: changing response',18,TEAL),text('Release to zero target',18,RED)).arrange(RIGHT,buff=.6).to_edge(DOWN,buff=.32)
  self.play(FadeIn(subtitle),Create(axes),FadeIn(zone),FadeIn(ticks),Create(walls),FadeIn(label),FadeIn(legends),run_time=1)
  curves=[]
  for row,color in zip(DATA['examples'],[GREEN,TEAL,RED]):
   pts=[axes.c2p(t,x)for t,x,*_ in row['samples']if t<=1.2]
   curves.append(VMobject(color=color,stroke_width=3.8).set_points_as_corners(pts))
  self.play(*[Create(c,rate_func=linear)for c in curves],run_time=6);self.wait(3)
  self.play(*[FadeOut(m)for m in list(self.mobjects)],run_time=.5)
  head=text('A checked handoff. A bounded region.',34).to_edge(UP,buff=.45)
  body=VGroup(text('After the admitted switch:',27,TEAL),
    text('Position stays between 3.26 cm and 14.365 cm.',27,GREEN),
    text('The controller aims for 8.81 cm. It may move backward.',21,MUTED),
    text('This is containment, not perfect rest at the stop point.',23,RED)).arrange(DOWN,buff=.37)
  details=VGroup(text('Model conditions: rate 8–12 /s; bounded target error;',18,MUTED),
    text('continuous state feedback; full-state handoff; stated sensor and delay bounds.',17,MUTED),
    text('The original brake-to-trigger proof and digital hold implementation remain open.',17,MUTED),
    text('Synthetic example. No hardware validation.',19,RED)).arrange(DOWN,buff=.14).to_edge(DOWN,buff=.4)
  self.play(FadeIn(head),FadeIn(body),run_time=1);self.play(FadeIn(details),run_time=.5);self.wait(7)
