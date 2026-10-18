"""Manim Community illustration, NOT a numerical proof of the theorem."""
from manim import *
import numpy as np
import math
import json
from pathlib import Path

BG = '#101820'
INK = '#EDF4F5'
MUTED = '#9DAFB9'
BACKUP = '#FFBF69'
CONTROL = '#59D8D0'
LIMIT = '#EE6C6C'
GREEN = '#A1DF94'
P = np.array([[38/5,257/25,5],[257/25,1319/50,769/50],[5,769/50,278/25]])
HANDOFF=1.25
H=.1
END=8.25
Z0=np.array([1.,.5,0.])

def held(t,z,u,r=1.):
    x,v,a=z
    b=(1-math.exp(-r*t))/r
    return np.array([x+v*t+u*t*t/2+(a-u)*(t-b)/r,
                     v+u*t+(a-u)*b, u+(a-u)*math.exp(-r*t)])

ZT=held(HANDOFF,Z0,-1.)
STATES=[ZT]
COMMANDS=[]
for n in range(72):
    z=STATES[-1]
    u=float(np.clip(-z[0]-3*z[1]-2*z[2],-1,1))
    COMMANDS.append(u)
    STATES.append(held(H, z, u))

def state(t):
    if t<=HANDOFF: return held(t,Z0,-1.)
    q=(t-HANDOFF)/H
    n=min(int(q),len(COMMANDS)-1)
    return held(t-HANDOFF-n*H,STATES[n],COMMANDS[n])

def energy(z): return float(z@P@z)

def txt(s,size=24,color=INK):
    return Text(s,font='Noto Sans',font_size=size,color=color)

def frame(title,subtitle):
    title=txt(title,36).to_edge(UP,buff=.38)
    subtitle=txt(subtitle,18,MUTED).next_to(title,DOWN,buff=.17)
    return VGroup(title,subtitle)

def curve(axes,fn,a,b,color):
    ts=np.linspace(a,b,max(2,int((b-a)*80)))
    return VMobject(color=color,stroke_width=4).set_points_as_corners([axes.c2p(t,fn(t)) for t in ts])

class RecoveryProof(Scene):
    def construct(self):
        self.camera.background_color=BG
        title=frame('Recover first. Then stay safe.',
                    'A checked recovery maneuver for a sampled controller with actuator lag')
        self.play(FadeIn(title,shift=UP*.2),run_time=.8)
        intro=VGroup(txt('Start outside the certified set.',32,BACKUP),
                     txt('Hold a recovery command. Enter the set.',30),
                     txt('Hand off without resetting the state.',30,CONTROL)).arrange(DOWN,buff=.46)
        intro.move_to(DOWN*.15)
        self.play(LaggedStart(*[FadeIn(m,shift=UP*.15) for m in intro],lag_ratio=.25),run_time=1.8)
        self.wait(2)
        self.play(FadeOut(intro),FadeOut(title),run_time=.6)

        header=frame('A single trajectory',
                     'Illustration: (x, v, a) = (1, 0.5, 0), fixed r = 1, post-handoff h = 0.1, errors = 0')
        self.add(header)
        rail=NumberLine(x_range=[-2,2,1],length=10.8,include_numbers=False,
                        include_tip=False,color=MUTED,stroke_width=2).move_to(UP*1.65)
        limits=VGroup(*[Line(rail.n2p(q)+UP*.3,rail.n2p(q)+DOWN*.3,color=LIMIT,stroke_width=4) for q in [-2,2]])
        railtext=VGroup(*[txt(str(q),19,LIMIT if abs(q)==2 else MUTED).next_to(rail.n2p(q)+DOWN*.3,DOWN,buff=.08) for q in [-2,0,2]])
        railtitle=txt('POSITION   |x| <= 2',21).next_to(rail,UP,buff=.35)
        bead=Dot(rail.n2p(1),radius=.095,color=BACKUP)
        railgroup=VGroup(rail,limits,railtext,railtitle,bead)
        self.play(FadeIn(railgroup),run_time=.6)

        xa=Axes(x_range=[0,8.25,2],y_range=[0,2,1],x_length=5.5,y_length=2.2,
                tips=False,axis_config={'color':MUTED,'include_numbers':False,'stroke_width':1}).move_to(LEFT*3.3+DOWN*.8)
        va=Axes(x_range=[0,8.25,2],y_range=[0,26,12],x_length=5.5,y_length=2.2,
                tips=False,axis_config={'color':MUTED,'include_numbers':False,'stroke_width':1}).move_to(RIGHT*3.3+DOWN*.8)
        labels=VGroup(txt('Position through time',22).next_to(xa,UP,buff=.2),
                      txt('Certificate energy  V = z^T P z',22).next_to(va,UP,buff=.2),
                      txt('0',16,MUTED).next_to(xa.c2p(0,0),DOWN,buff=.12),
                      txt('8.25',16,MUTED).next_to(xa.c2p(8.25,0),DOWN,buff=.12),
                      txt('normalized time',16,MUTED).next_to(xa,DOWN,buff=.4),
                      txt('0',16,MUTED).next_to(va.c2p(0,0),DOWN,buff=.12),
                      txt('8.25',16,MUTED).next_to(va.c2p(8.25,0),DOWN,buff=.12),
                      txt('normalized time',16,MUTED).next_to(va,DOWN,buff=.4))
        xlim=DashedLine(xa.c2p(0,2),xa.c2p(8.25,2),color=LIMIT,stroke_width=2)
        x2=txt('2',16,LIMIT).next_to(xa.c2p(0,2),LEFT,buff=.12)
        threshold=DashedLine(va.c2p(0,12),va.c2p(8.25,12),color=GREEN,stroke_width=2)
        thlabel=txt('12',18,GREEN).next_to(va.c2p(0,12),LEFT,buff=.12)
        self.add(xa,va,labels,xlim,x2,threshold,thlabel)
        t=ValueTracker(0)
        xfull=curve(xa,lambda q:state(q)[0],0,HANDOFF,BACKUP)
        vfull=curve(va,lambda q:energy(state(q)),0,HANDOFF,BACKUP)
        xd=Dot(xa.c2p(0,1),radius=.055,color=BACKUP)
        vd=Dot(va.c2p(0,energy(Z0)),radius=.055,color=BACKUP)
        bead.add_updater(lambda m:m.move_to(rail.n2p(state(t.get_value())[0])))
        xd.add_updater(lambda m:m.move_to(xa.c2p(t.get_value(),state(t.get_value())[0])))
        vd.add_updater(lambda m:m.move_to(va.c2p(t.get_value(),energy(state(t.get_value())))))
        badge=txt('RECOVERY   u = -1   |   0 <= t <= 1.25',23,BACKUP).move_to(DOWN*3.05)
        note=txt('Initial V = 24.475 > 12: outside the old certified set.',19,MUTED).move_to(DOWN*3.48)
        self.add(xd,vd,badge,note)
        self.play(Create(xfull),Create(vfull),t.animate.set_value(HANDOFF),run_time=5,rate_func=linear)
        self.wait(.4)
        switch=VGroup(DashedLine(xa.c2p(HANDOFF,0),xa.c2p(HANDOFF,2),color=INK,stroke_width=1.4),
                      DashedLine(va.c2p(HANDOFF,0),va.c2p(HANDOFF,26),color=INK,stroke_width=1.4))
        newbadge=txt('HANDOFF at t = 1.25   |   V = %.3f < 12'%energy(ZT),23,CONTROL).move_to(badge)
        newnote=txt('v = %.3f, a = %.3f: not at rest. Position, velocity and acceleration stay continuous.'%(ZT[1],ZT[2]),17,MUTED).move_to(note)
        self.play(FadeIn(switch),Transform(badge,newbadge),Transform(note,newnote),bead.animate.set_color(CONTROL),run_time=.8)
        self.wait(3)
        tailx=curve(xa,lambda q:state(q)[0],HANDOFF,END,CONTROL)
        tailv=curve(va,lambda q:energy(state(q)),HANDOFF,END,CONTROL)
        self.play(Transform(badge,txt('SAMPLED FEEDBACK   u = clip(-x - 3v - 2a) at each sample',21,CONTROL).move_to(badge)),run_time=.6)
        self.play(Create(tailx),Create(tailv),t.animate.set_value(END),run_time=8,rate_func=linear)
        self.wait(1)
        bead.clear_updaters();xd.clear_updaters();vd.clear_updaters()
        self.play(*[FadeOut(m) for m in list(self.mobjects)],run_time=.7)

        final=frame('One trajectory illustrates it. Lean proves the box.',
                    'The proof covers every continuous execution satisfying the stated model.')
        self.add(final)
        box=RoundedRectangle(width=6.25,height=2.25,corner_radius=.15,color=BACKUP,fill_opacity=.04).move_to(LEFT*3.25+UP*.35)
        boxtext=VGroup(txt('EVERY INITIAL STATE IN',20,BACKUP),
                      txt('x in [0.99, 1.01]',26),txt('v in [0.49, 0.51]',26),txt('a in [-0.01, 0.01]',26)).arrange(DOWN,buff=.16).move_to(box)
        result=VGroup(txt('RECOVER  ->  HAND OFF',22,CONTROL),txt('|x(t)| <= 2',40,GREEN),txt('for every t >= 0',24)).arrange(DOWN,buff=.3).move_to(RIGHT*3.35+UP*.35)
        self.play(FadeIn(box),FadeIn(boxtext),FadeIn(result),run_time=.8)
        assumptions=VGroup(txt('Fixed r in [0.9, 1.1]; exact backup u = -1 with zero error.',20),
                           txt('After handoff: 0 < h_min <= h_n <= 0.2.',20),
                           txt('Held request error e and command error d: |e_n| + |d_n| <= 1/90.',20),
                           txt('Continuous state; actual own-sample feedback; same fixed plant rate.',20)).arrange(DOWN,buff=.24).move_to(DOWN*1.85)
        self.play(FadeIn(assumptions,shift=UP*.1),run_time=.7)
        footer=txt('Model guarantee, not hardware validation. No claim of optimality or controller superiority.',16,MUTED).to_edge(DOWN,buff=.24)
        self.add(footer)
        self.wait(7)

if __name__=='__main__':
    samples=[state(float(t)) for t in np.linspace(0,END,1651)]
    summary={'role':'Floating-point illustration only; theorem proved separately in Lean',
        'initial':[float(x) for x in Z0],'rate':1,'backup_command':-1,'handoff_time':HANDOFF,
        'tail_hold':H,'errors':0,'initial_energy':energy(Z0),'terminal_state':ZT.tolist(),
        'terminal_energy':energy(ZT),'sampled_max_abs_position':max(abs(z[0]) for z in samples),
        'render_end_time':END,'tail_final_state':state(END).tolist()}
    Path(__file__).with_name('trajectory-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
