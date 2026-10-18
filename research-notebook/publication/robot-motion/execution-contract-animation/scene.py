from pathlib import Path
import json
import numpy as np
from manim import *

config.background_color='#0D1724'
FONT='DejaVu Sans'
WHITE_SOFT='#E9F0F7'
MUTED='#AAB7C5'

def text(s,size=26,color=WHITE_SOFT):
    return Text(s,font=FONT,font_size=size,color=color)

class MotionContracts(Scene):
    def construct(self):
        data=json.loads((Path(__file__).parent/'data.json').read_text())['methods']
        title=text('Same goal. Different motion.',36).to_edge(UP,buff=.35)
        subtitle=text('A simulated single-axis actuator',23,MUTED).next_to(title,DOWN,buff=.18)
        footer=text('Offline comparison: calculation delay is omitted. No robot test.',17,MUTED).to_edge(DOWN,buff=.22)
        self.play(FadeIn(title),FadeIn(subtitle),FadeIn(footer),run_time=1)
        self.wait(1)
        clock=ValueTracker(0)
        number=DecimalNumber(0,num_decimal_places=2,font_size=28).set_color(WHITE_SOFT)
        number.add_updater(lambda m:m.set_value(clock.get_value()))
        readout=VGroup(text('Simulated time',22,MUTED),number,text('s',22,MUTED)).arrange(RIGHT,buff=.15).move_to([3.5,2.15,0])
        labels=VGroup();rails=VGroup();dots=VGroup();goals=VGroup()
        x0=-3.25;scale=.445
        for i,item in enumerate(data):
            y=1.15-i*1.1
            label=text(item['label'],21,item['color']).move_to([-5.12,y,0]);labels.add(label)
            rail=Line([x0,y,0],[x0+20*scale,y,0],color='#415469',stroke_width=2)
            rails.add(rail)
            times=np.array([s['t']for s in item['samples']]);positions=np.array([s['x_mm']for s in item['samples']])
            dot=Dot([x0,y,0],radius=.095,color=item['color'])
            dot.add_updater(lambda m,times=times,positions=positions,y=y:m.move_to([x0+scale*np.interp(clock.get_value(),times,positions),y,0]))
            dots.add(dot)
            goal=Rectangle(width=.08,height=.48,color='#7B91A9',fill_opacity=.25,stroke_width=1).move_to([x0+20*scale,y,0]);goals.add(goal)
        ticks=VGroup()
        for mm in [0,5,10,15,20]:
            ticks.add(text(str(mm),18,MUTED).move_to([x0+scale*mm,-2.72,0]))
        axislabel=text('Actual position (mm)',20,MUTED).move_to([1.25,-3.12,0])
        legend=text('Initial requested goal: 20 mm',22,MUTED).move_to([-.95,2.15,0])
        content=VGroup(labels,rails,dots,goals,ticks,axislabel,legend,readout)
        self.play(FadeIn(content),run_time=.7)
        self.play(clock.animate.set_value(.52),run_time=4,rate_func=linear)
        request=text('New goal: return to 0 mm',25,WHITE_SOFT).move_to(legend)
        self.play(Transform(legend,request),*[g.animate.set_x(x0)for g in goals],run_time=.7)
        self.wait(1.3)
        self.play(clock.animate.set_value(1.70),run_time=9,rate_func=linear)
        passed=text('All four pass this generous 1.70 s sampled task.',22,'#42C6A2').move_to([0,2.15,0])
        self.play(FadeOut(legend),FadeOut(readout),FadeIn(passed),run_time=.5)
        self.wait(1.5)
        for dot in dots:dot.clear_updaters()
        number.clear_updaters()
        self.play(FadeOut(content),FadeOut(passed),FadeOut(subtitle),run_time=.7)
        headline=text('Which kind of smoothness?',36).move_to(title)
        self.play(Transform(title,headline),run_time=.5)
        columns=[-4.8,-1.6,1.25,4.35]
        headers=['Method','Jerk² integral','Extra travel','Peak jerk']
        units=['','m²/s⁵','mm','m/s³']
        table=VGroup()
        for x,label,unit in zip(columns,headers,units):
            table.add(text(label,22).move_to([x,1.9,0]))
            if unit:table.add(text(unit,19,MUTED).move_to([x,1.48,0]))
        for i,item in enumerate(data):
            y=.65-i*.73
            values=[item['label'],f"{item['jerk_integral']:.2f}",f"{item['extra_travel_mm']:.2f}",f"{item['peak_jerk']:.2f}"]
            for x,value in zip(columns,values):table.add(text(value,22,item['color']).move_to([x,y,0]))
        note=text('Same plant and moving start; metrics cover 0.52–2.50 s.',20,MUTED).move_to([0,-2.5,0])
        insight=text('A lower integral can still have a higher peak.',25).move_to([0,-3.03,0])
        self.play(FadeIn(table),FadeIn(note),FadeIn(insight),run_time=.8)
        self.wait(5.5)
        self.play(FadeOut(table),FadeOut(note),FadeOut(insight),run_time=.6)
        self.play(Transform(title,text('Three claims need three checks.',36).move_to(title)),run_time=.6)
        boxes=VGroup()
        for x,heading,body,color in [(-4.35,'Task','Goal and deadline','#E7A144'),(0,'Reference','Limits and timing','#6299EA'),(4.35,'Actual motion','Model and uncertainty','#42C6A2')]:
            box=RoundedRectangle(width=3.8,height=1.9,corner_radius=.15,color=color,stroke_width=2).move_to([x,.35,0])
            boxes.add(VGroup(box,text(heading,30,color).move_to([x,.75,0]),text(body,20).move_to([x,-.02,0])))
        final=text('A smooth curve alone does not prove task success.',25).move_to([0,-1.65,0])
        credit=text('Illustrative research data · Made with Manim Community',17,MUTED).move_to([0,-2.55,0])
        self.play(LaggedStart(*[FadeIn(b)for b in boxes],lag_ratio=.2),FadeIn(final),FadeIn(credit),run_time=1.1)
        self.wait(4)
