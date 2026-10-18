"""Explain the proved model and one numerical trace. Not a robot measurement."""
from pathlib import Path
import json
import numpy as np
from manim import *
BG = '#101c29'
INK = '#edf3f5'
MUTED = '#a9b9c7'
TEAL = '#57d0c5'
AMBER = '#f6c777'
RED = '#f19891'

def text(s, size=25, color=INK):
    return Text(s, font='Noto Sans', font_size=size, color=color)

def box(title, detail, color):
    frame = RoundedRectangle(width=3.45, height=1.7, corner_radius=.14,
                             stroke_color=color, fill_color='#1b2e3d', fill_opacity=1)
    labels = VGroup(text(title, 25, color), text(detail, 17, MUTED)).arrange(DOWN,buff=.20)
    if labels.width > 3.03: labels.scale_to_fit_width(3.03)
    if labels.height > 1.4: labels.scale_to_fit_height(1.4)
    return VGroup(frame, labels)

class ChangingPlans(Scene):
    def clear(self, scope):
        self.play(*[FadeOut(m) for m in list(self.mobjects) if m is not scope],run_time=.4)

    def construct(self):
        self.camera.background_color = BG
        scope = text('Checked model + illustrative simulation. No hardware claim.',17,MUTED).to_edge(DOWN,buff=.2)
        title = text('When plans change, how far can a robot stray?',34).to_edge(UP,buff=.5)
        cards = VGroup(box('Smooth plan','position, speed\nand acceleration',TEAL),
                       box('Tracking controller','correct error\n+ feed forward jerk',AMBER),
                       box('Axis with lag','response changes\nwithin a rate band',INK)).arrange(RIGHT,buff=.8).move_to(UP*.3)
        arrows = VGroup(*[Arrow(cards[i].get_right(),cards[i+1].get_left(),buff=.1,color=MUTED,stroke_width=2) for i in range(2)])
        promise = text('The proof bounds the difference between planned and actual motion.',25,TEAL).move_to(DOWN*1.35)
        switch = text('At each replan: match the old reference. Keep the actual state.',22,MUTED).move_to(DOWN*2.05)
        self.play(FadeIn(title),FadeIn(cards),Create(arrows),FadeIn(promise),FadeIn(switch),FadeIn(scope),run_time=.7)
        self.wait(4.5)
        self.clear(scope)

        data = json.loads(Path('comparison-trace.json').read_text())['methods']['reciprocal_midpoint']
        samples = data['samples']; R = data['metrics']['sufficient_radius_m']*1000
        ts = np.array([s['t_s'] for s in samples]); xs = np.array([s['x_m']*1000 for s in samples])
        def q(t):
            state = [0.,0.,0.]
            for j in [10.,-10.,-10.,10.]:
                h=min(max(t,0.),.02)
                p,v,a=state
                state=[p+v*h+a*h*h/2+j*h*h*h/6,v+a*h+j*h*h/2,a+j*h]
                t-=h
                if t<=1e-12:break
            return state[0]*1000
        title = text('A small move, with room for error',34).to_edge(UP,buff=.32)
        subtitle = text('0.16 mm move • four 20 ms segments • actual lag rate: 80 to 120 / s',21,MUTED).next_to(title,DOWN,buff=.18)
        axes=Axes(x_range=[0,.3,.05],y_range=[-.15,.35,.1],x_length=7,y_length=3.7,tips=False,
                  axis_config={'stroke_color':MUTED,'stroke_width':1.2}).move_to(LEFT*2.35+DOWN*.2)
        marks=VGroup(*[text(f'{y:.1f}',16,MUTED).next_to(axes.c2p(0,y),LEFT,buff=.13)for y in [-.1,0,.1,.2,.3]],
                     *[text(str(int(t*1000)),16,MUTED).next_to(axes.c2p(t,-.15),DOWN,buff=.13)for t in [0,.1,.2,.3]])
        labels=VGroup(text('Position (mm)',18,MUTED).move_to(LEFT*4.9+UP*1.98),
                      text('Time (ms)',18,MUTED).move_to(LEFT*2.3+DOWN*2.65))
        grid=np.linspace(0,.3,240)
        band=Polygon(*[axes.c2p(t,q(t)+R)for t in grid],*[axes.c2p(t,q(t)-R)for t in grid[::-1]],
                     fill_color=TEAL,fill_opacity=.12,stroke_width=0)
        qp=VMobject(color=TEAL,stroke_width=2).set_points_as_corners([axes.c2p(t,q(t))for t in grid])
        xp=VMobject(color=AMBER,stroke_width=3).set_points_as_corners([axes.c2p(t,np.interp(t,ts,xs))for t in grid])
        joins=VGroup(*[DashedLine(axes.c2p(t,-.15),axes.c2p(t,.35),color=MUTED,stroke_width=.8)for t in [.02,.04,.06,.08]])
        stats=VGroup(text('Allowed error',23,MUTED),text(f'± {R:.4f} mm',34,TEAL),
                     text('This trace: peak error',21,MUTED),text('0.0161 mm',31,AMBER),
                     text('The whole tube is proved.',21,TEAL),text('This line is simulated.',21,AMBER)).arrange(DOWN,buff=.25).move_to(RIGHT*4.05+DOWN*.15)
        legend=VGroup(text('— plan',19,TEAL),text('— actual model trace',19,AMBER),text('Shading: allowed tube',18,MUTED)).arrange(RIGHT,buff=.45).move_to(DOWN*3.1)
        self.play(FadeIn(title),FadeIn(subtitle),Create(axes),FadeIn(marks),FadeIn(labels),FadeIn(band),Create(joins),FadeIn(stats),FadeIn(legend),run_time=.6)
        self.play(Create(qp),Create(xp),run_time=5,rate_func=linear)
        self.wait(3)
        self.clear(scope)

        title=text('A tighter proof bound is not always better tracking.',32).to_edge(UP,buff=.5)
        a=box('Short move, slow axis','worst of four tested\nrate signals',RED)
        b=box('Long move, faster axis','worst of four tested\nrate signals',TEAL)
        cards=VGroup(a,b).arrange(RIGHT,buff=1.4).move_to(UP*.55)
        lines=VGroup(
            VGroup(text('Without jerk FF: 0.112 mm',23),text('Midpoint jerk FF: 1.960 mm',23,RED)).arrange(DOWN,buff=.25).next_to(a,DOWN,buff=.35),
            VGroup(text('Without jerk FF: 0.156 mm',23),text('Midpoint jerk FF: 0.0267 mm',23,TEAL)).arrange(DOWN,buff=.25).next_to(b,DOWN,buff=.35))
        note=text('Both keep acceleration feedforward. These are numerical comparisons.',21,MUTED).move_to(DOWN*2.5)
        self.play(FadeIn(title),FadeIn(cards),FadeIn(lines),FadeIn(note),run_time=.6)
        self.wait(5)
        self.clear(scope)
        title=text('Finished: the finite-replan tracking proof.',35,TEAL).move_to(UP*1.25)
        body=VGroup(text('34 checked statements. Explicit physical assumptions.',25),
                    text('Next: connect the sampled controller to those assumptions.',25),
                    text('Then test an identified axis.',25)).arrange(DOWN,buff=.45).move_to(DOWN*.4)
        self.play(FadeIn(title),FadeIn(body),run_time=.6)
        self.wait(4)
