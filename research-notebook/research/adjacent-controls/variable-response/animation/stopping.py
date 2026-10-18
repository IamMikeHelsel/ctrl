"""Manim Community explanation. Traces illustrate; Lean proves separately."""
from manim import *
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
DATA=json.loads((HERE.parent/'results.json').read_text())
BG='#101820';INK='#EDF4F5';MUTED='#A7B7BC';GREEN='#8FDCAB';TEAL='#68C9D2';RED='#F49075'

def label(s,size=25,color=INK):return Text(s,font='Noto Sans',font_size=size,color=color)


class ChangingResponse(Scene):
    def construct(self):
        self.camera.background_color=BG
        title=label('Same command. Different response.',38).to_edge(UP,buff=.45)
        intro=VGroup(label('How much room do we need?',32),
            label('Allow for delay, sensor error and weaker braking.',25,MUTED),
            label('Then check the whole motion before the first stop.',25,TEAL)).arrange(DOWN,buff=.4)
        self.play(FadeIn(title),FadeIn(intro),run_time=1)
        self.wait(3)
        self.play(FadeOut(intro),run_time=.5)
        subtitle=label('Synthetic powered axis  |  0.40 m/s estimate  |  50 ms maximum delay',19,MUTED).next_to(title,DOWN,buff=.2)
        self.add(subtitle)
        axes=Axes(x_range=[0,.7,.1],y_range=[0,.20,.05],x_length=10.4,y_length=3.7,
          tips=False,axis_config={'color':MUTED,'include_numbers':False,'stroke_width':1.5}).move_to(DOWN*.05)
        ticklabels=VGroup(*[label(str(round(t,1)),15,MUTED).next_to(axes.c2p(t,0),DOWN,buff=.12)for t in [0,.2,.4,.6]],
          *[label(f'{int(100*x)} cm',15,MUTED).next_to(axes.c2p(0,x),LEFT,buff=.15)for x in [.05,.10,.15,.20]])
        xlabel=label('Seconds from the stop request',17,MUTED).next_to(axes,DOWN,buff=.55)
        wall=DashedLine(axes.c2p(0,.15),axes.c2p(.7,.15),color=RED,stroke_width=2)
        walllabel=label('15 cm position limit',19,RED).next_to(axes.c2p(.12,.15),UP,buff=.1)
        self.play(Create(axes),FadeIn(ticklabels),FadeIn(xlabel),Create(wall),FadeIn(walllabel),run_time=1)
        names=['smooth_rate_and_target','slow_weak_endpoint','out_of_contract_strength']
        colors=[TEAL,GREEN,RED]
        descriptions=['Changing response within bounds','Worst admitted response','Weaker than the assumed bound']
        curves=[];ends=[];legend=[]
        for name,color,desc in zip(names,colors,descriptions):
            row=next(t for t in DATA['traces']if t['name']==name)
            stop=row['stop'];sstop=stop['time_from_request_s']
            coords=[axes.c2p(0,.001),axes.c2p(.05,.021625)]
            coords += [axes.c2p(s+.05,x)for s,x,v,a in row['samples']if s+.05<sstop]
            coords.append(axes.c2p(sstop,stop['peak_position_m']))
            curves.append(VMobject(color=color,stroke_width=4).set_points_as_corners(coords))
            ends.append(Dot(coords[-1],radius=.055,color=color))
            legend.append(label(desc,18,color))
        legends=VGroup(*legend).arrange(RIGHT,buff=.45).to_edge(DOWN,buff=.28)
        self.play(FadeIn(legends),run_time=.5)
        self.play(*[Create(c,rate_func=linear)for c in curves],run_time=7)
        self.play(*[FadeIn(e)for e in ends],run_time=.4)
        self.wait(3)
        self.play(*[FadeOut(o)for o in list(self.mobjects)],run_time=.6)
        head=label('What the proof establishes',36).to_edge(UP,buff=.5)
        card=VGroup(label('Every admitted changing response:',29,TEAL),
            label('First zero velocity within 0.55 seconds.',29),
            label('Position stays at or below 15 cm until then.',27,GREEN),
            label('The limit is relative to the measured starting reference.',19,MUTED),
            label('Remaining stopped needs a separate holding guarantee.',24,RED)).arrange(DOWN,buff=.33)
        card.move_to(UP*.15)
        assumptions=VGroup(label('Assumptions: position error ±1 mm; velocity error ±0.01 m/s;',18,MUTED),
            label('delay ≤50 ms; pending acceleration ≤0.1 m/s²;',18,MUTED),
            label('response rate 8–12 /s; effective target at most −1.2 m/s².',18,MUTED),
            label('A mathematical model result. No hardware or PL d/e claim.',19,RED)).arrange(DOWN,buff=.12).to_edge(DOWN,buff=.33)
        self.play(FadeIn(head),LaggedStart(*[FadeIn(m)for m in card],lag_ratio=.15),run_time=1.8)
        self.play(FadeIn(assumptions),run_time=.6)
        self.wait(7)
