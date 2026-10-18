"""Public explanation of a target-selection contract, not robot motion."""
from manim import *

BG = '#101820'
INK = '#EDF4F5'
MUTED = '#A7B7BC'
GREEN = '#8FDCAB'
TEAL = '#68C9D2'
AMBER = '#F5C978'


def txt(s, size=25, color=INK):
    return Text(s, font='Noto Sans', font_size=size, color=color)


def card(heading, value, detail, color=TEAL):
    box = RoundedRectangle(width=3.65, height=2.15, corner_radius=.16,
                           stroke_color=color, stroke_width=1.5,
                           fill_color='#182731', fill_opacity=1)
    labels = VGroup(txt(heading, 21, MUTED), txt(value, 35, color),
                    txt(detail, 17, MUTED)).arrange(DOWN, buff=.23)
    return VGroup(box, labels)


class SteadyEnough(Scene):
    def clear_content(self, scope):
        self.play(*[FadeOut(m) for m in list(self.mobjects) if m is not scope], run_time=.4)

    def construct(self):
        self.camera.background_color = BG
        scope = txt('Target selection only • not a robot simulation', 18, MUTED).to_edge(DOWN, buff=.22)
        title = txt('Steady enough to move', 44).move_to(UP*.5)
        intro = txt('Keep a target until a change is large enough.', 27, TEAL).next_to(title, DOWN, buff=.45)
        self.play(FadeIn(title), FadeIn(intro), FadeIn(scope), run_time=.5)
        self.wait(1.1)
        self.clear_content(scope)

        title = txt('Small noisy proposals. One retained target.', 34).to_edge(UP, buff=.4)
        subtitle = txt('Fixed intended target: 0 mm   |   proposal error: ±0.5 mm', 21, MUTED).next_to(title, DOWN, buff=.2)
        axes = Axes(x_range=[0, 8, 1], y_range=[-2.4, 2.4, 1],
                    x_length=9.5, y_length=3.7, tips=False,
                    axis_config={'stroke_color': MUTED, 'stroke_width': 1.2}).move_to(DOWN*.1)
        marks = VGroup(*[txt(str(y), 17, MUTED).next_to(axes.c2p(0,y), LEFT, buff=.16)
                        for y in [-2, 0, 2]])
        ylabel = txt('Offset (mm)', 18, MUTED).move_to(LEFT*5.65+UP*1.95)
        xlabel = txt('Successive proposals', 18, MUTED).move_to(DOWN*2.28)
        gates = VGroup(*[DashedLine(axes.c2p(0,y), axes.c2p(8,y),
                                    color=AMBER, stroke_width=1.8, dash_length=.10)
                        for y in [-2,2]])
        anchor = Line(axes.c2p(0,0), axes.c2p(8,0), color=GREEN, stroke_width=3)
        legend = VGroup(txt('● proposal', 19, TEAL), txt('— retained anchor', 19, GREEN),
                        txt('– – gate at ±2 mm', 19, AMBER)).arrange(RIGHT,buff=.6).move_to(DOWN*2.78)
        rule = txt('Accept only when |proposal − anchor| > 2 mm', 22).move_to(DOWN*3.12)
        self.play(FadeIn(title), FadeIn(subtitle), Create(axes), FadeIn(marks),
                  FadeIn(ylabel), FadeIn(xlabel), Create(gates), Create(anchor),
                  FadeIn(legend), FadeIn(rule), run_time=.6)
        values = [.5,-.5,.35,-.4,.1,.5,-.25,.45]
        for i, y in enumerate(values, 1):
            dot = Dot(axes.c2p(i,y), radius=.065, color=TEAL)
            self.play(FadeIn(dot, scale=.5), run_time=.2)
            self.wait(.15)
        self.wait(2)
        self.clear_content(scope)

        title = txt('A clear target change passes the gate.', 35).to_edge(UP, buff=.45)
        subtitle = txt('The intended target moves by 20 mm.', 26, TEAL).next_to(title, DOWN, buff=.3)
        row = VGroup(card('Old anchor', '0 mm', 'retained target', GREEN),
                     card('Valid proposal', '19.8 mm', 'within 0.5 mm of 20 mm'),
                     card('Gate decision', 'ACCEPT', '19.8 mm > 2 mm', GREEN)).arrange(RIGHT, buff=.35).move_to(UP*.1)
        line1 = txt('Passes at the next valid proposal.', 26, GREEN).move_to(DOWN*1.8)
        line2 = txt('The motion controller must still check a feasible path.', 23, MUTED).move_to(DOWN*2.45)
        self.play(FadeIn(title), FadeIn(subtitle), FadeIn(row), FadeIn(line1), FadeIn(line2), run_time=.6)
        self.wait(4)
        self.clear_content(scope)

        title = txt('The cost: a small intended move can be ignored.', 32).to_edge(UP, buff=.45)
        subtitle = txt('Separate example: anchor 0 mm, intended target 1 mm.', 23, MUTED).next_to(title, DOWN, buff=.28)
        row = VGroup(card('Old anchor', '0 mm', 'retained target', GREEN),
                     card('Valid proposal', '1.3 mm', 'within 0.5 mm of 1 mm'),
                     card('Gate decision', 'KEEP 0 mm', '1.3 mm ≤ 2 mm', AMBER)).arrange(RIGHT,buff=.35).move_to(UP*.1)
        line1 = txt('Rejecting jitter also limits target resolution.', 26, AMBER).move_to(DOWN*1.8)
        line2 = txt('The threshold must fit the task.', 23, MUTED).move_to(DOWN*2.45)
        self.play(FadeIn(title), FadeIn(subtitle), FadeIn(row), FadeIn(line1), FadeIn(line2), run_time=.6)
        self.wait(4)
        self.clear_content(scope)

        title = txt('A gate is one part of steady motion.', 35).to_edge(UP,buff=.5)
        box1 = RoundedRectangle(width=3.1,height=1.65,corner_radius=.15,stroke_color=GREEN,fill_color='#182731',fill_opacity=1)
        box2 = box1.copy().set_stroke(TEAL)
        box3 = box1.copy().set_stroke(MUTED)
        boxes = VGroup(box1, box2, box3).arrange(RIGHT,buff=1.05).move_to(UP*.45)
        labels = VGroup(
            txt('Target gate',25,GREEN).move_to(box1),
            VGroup(txt('Smooth feasible',23,TEAL),txt('motion',23,TEAL)).arrange(DOWN,buff=.15).move_to(box2),
            VGroup(txt('Physical tracking',22),txt('+ stop reserve',22)).arrange(DOWN,buff=.15).move_to(box3))
        arrows = VGroup(Arrow(box1.get_right(),box2.get_left(),buff=.12,stroke_width=2,color=MUTED),
                        Arrow(box2.get_right(),box3.get_left(),buff=.12,stroke_width=2,color=MUTED))
        checked = txt('Checked: target gate + fixed-hold composition.',25,GREEN).move_to(DOWN*1.3)
        open_work = txt('The full moving and contact chain remains open.',23,MUTED).move_to(DOWN*1.95)
        no_claim = txt('A quiet target does not prove a vibration-free arm.',23,AMBER).move_to(DOWN*2.6)
        self.play(FadeIn(title),FadeIn(boxes),FadeIn(labels),Create(arrows),FadeIn(checked),FadeIn(open_work),FadeIn(no_claim),run_time=.6)
        self.wait(5)
