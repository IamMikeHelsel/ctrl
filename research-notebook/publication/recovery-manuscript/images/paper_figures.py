"""Static print figures rendered by Manim Community; trajectories are illustrations.
Imports the existing animation model through the read-only /animation mount.
"""
from manim import *
import sys
sys.path.insert(0, '/animation')
import recovery as model

config.frame_width=16
config.frame_height=8.5
INK='#172D35';MUTED='#4C6067';TEAL='#087F82';ORANGE='#A95B00';RED='#B33135';GRID='#CBD4D7'

def text(s,size=25,color=INK):
    return Text(s,font='Noto Sans',font_size=size,color=color)
def arrow(a,b,color=INK):
    return Arrow(a,b,buff=.08,stroke_width=2.4,max_tip_length_to_length_ratio=.12,color=color)
def box(center,width,height,label,size=24,color=INK):
    frame=RoundedRectangle(width=width,height=height,corner_radius=.10,color=color,stroke_width=2).move_to(center)
    caption=text(label,size,color).move_to(center)
    return VGroup(frame,caption)
def plot(axes,fn,a,b,color):
    return VMobject(color=color,stroke_width=3.6).set_points_as_corners(
        [axes.c2p(t,fn(t)) for t in np.linspace(a,b,max(2,int((b-a)*150)))])

class CarriageModel(Scene):
    def construct(self):
        self.camera.background_color=WHITE
        self.add(text('One-axis carriage with actuator lag',35).move_to([0,3.72,0]))
        self.add(text('A normalized model of motion, command limits, and a control handoff',22,MUTED).move_to([0,3.12,0]))
        rail=Line([-5.7,1.7,0],[5.7,1.7,0],color=MUTED,stroke_width=4)
        self.add(rail)
        for xpos,label in [(-5.7,'x = -2'),(0,'0'),(5.7,'x = +2')]:
            self.add(Line([xpos,1.4,0],[xpos,2.05,0],color=RED if xpos else MUTED,stroke_width=3))
            self.add(text(label,23,RED if xpos else MUTED).move_to([xpos,1.03,0]))
        self.add(text('travel limit',20,RED).move_to([-5.7,2.4,0]),text('travel limit',20,RED).move_to([5.7,2.4,0]))
        carriage=RoundedRectangle(width=1.45,height=.62,corner_radius=.08,color=INK,fill_color='#E5F1F0',fill_opacity=1).move_to([2.6,2.12,0])
        wheels=VGroup(*[Circle(radius=.12,color=INK,fill_color=WHITE,fill_opacity=1).move_to([q,1.78,0]) for q in (2.12,3.08)])
        self.add(carriage,wheels,text('carriage',21).move_to(carriage))
        self.add(arrow([3.45,2.1,0],[4.65,2.1,0],TEAL),text('velocity v',20,TEAL).move_to([4.1,2.65,0]))
        self.add(DoubleArrow([0,.48,0],[2.6,.48,0],buff=0,color=INK,stroke_width=2),text('position x',21).move_to([1.3,.11,0]))
        self.add(text('acceleration a changes velocity',20,MUTED).move_to([-3.2,.35,0]))
        y=-1.35
        control=box([-5.62,y,0],3.35,1.05,'Backup: u = -1\nSwitch at T\nSampled feedback',21,ORANGE)
        lag=box([-1.67,y,0],3.05,1.05,"Actuator lag\na' = r(u - a)",24)
        velocity=box([1.95,y,0],2.25,1.05,"Velocity\nv' = a",24)
        position=box([5.25,y,0],2.25,1.05,"Position\nx' = v",24)
        self.add(control,lag,velocity,position)
        for left,right,label in [(control,lag,'u'),(lag,velocity,'a'),(velocity,position,'v')]:
            a=arrow(left.get_right(),right.get_left());self.add(a,text(label,25).next_to(a,UP,buff=.10))
        self.add(arrow(position.get_right(),[7.25,y,0]),text('x',25).move_to([7.28,-.91,0]))
        feedback=VMobject(color=TEAL,stroke_width=2).set_points_as_corners([[5.25,-1.88,0],[5.25,-2.65,0],[-5.62,-2.65,0],[-5.62,-1.98,0]])
        self.add(feedback,arrow([-5.62,-2.25,0],[-5.62,-1.88,0],TEAL))
        for sx in (.34,3.60):
            self.add(Line([sx,y,0],[sx,-2.65,0],color=TEAL,stroke_width=2),Dot([sx,y,0],radius=.035,color=TEAL))
        self.add(text('After T: sample z = (x, v, a), then hold u = clip(-x - 3v - 2a)',22,TEAL).move_to([0,-3.15,0]))
        self.add(text('clip limits the command to [-1, 1].  State stays continuous at the switch.',21,MUTED).move_to([0,-3.67,0]))

class NominalTrace(Scene):
    def construct(self):
        self.camera.background_color=WHITE
        self.add(text('Nominal recovery and handoff',35).move_to([0,3.74,0]))
        self.add(text('Illustration only: r = 1; z(0) = (1, 0.5, 0); T = 1.25; post-handoff h = 0.1; errors = 0',21,MUTED).move_to([0,3.15,0]))
        self.add(Line([-3.9,2.57,0],[-3.25,2.57,0],color=ORANGE,stroke_width=4),text('backup: u = -1',22,ORANGE).move_to([-1.9,2.57,0]))
        self.add(Line([.25,2.57,0],[.9,2.57,0],color=TEAL,stroke_width=4),text('sampled feedback',22,TEAL).move_to([2.4,2.57,0]))
        xa=Axes(x_range=[0,8.25,2],y_range=[-2,2,1],x_length=6.15,y_length=3.6,tips=False,
            axis_config={'color':MUTED,'include_numbers':False,'stroke_width':1.5}).move_to([-3.75,-.05,0])
        va=Axes(x_range=[0,8.25,2],y_range=[0,26,6],x_length=6.15,y_length=3.6,tips=False,
            axis_config={'color':MUTED,'include_numbers':False,'stroke_width':1.5}).move_to([3.75,-.05,0])
        self.add(xa,va)
        for ax,title in [(xa,'Position x'),(va,'Certificate energy V = z^T P z')]:
            self.add(text(title,25).next_to(ax,UP,buff=.19))
            for t in (0,2,4,6,8):
                self.add(text(str(t),19,MUTED).move_to(ax.c2p(t,ax.y_range[0])+DOWN*.25))
            self.add(text('normalized time t',21,MUTED).next_to(ax,DOWN,buff=.55))
        for q in (-2,0,2):self.add(text(str(q),20,RED if abs(q)==2 else MUTED).next_to(xa.c2p(0,q),LEFT,buff=.14))
        for q in (0,12,24):self.add(text(str(q),20,TEAL if q==12 else MUTED).next_to(va.c2p(0,q),LEFT,buff=.14))
        for q in (-2,2):self.add(DashedLine(xa.c2p(0,q),xa.c2p(8.25,q),color=RED,stroke_width=2,dash_length=.12))
        self.add(DashedLine(va.c2p(0,12),va.c2p(8.25,12),color=TEAL,stroke_width=2,dash_length=.12))
        self.add(text('V = 12',20,TEAL).move_to(va.c2p(6.6,12)+UP*.24))
        for ax,fn in [(xa,lambda t:model.state(t)[0]),(va,lambda t:model.energy(model.state(t)))]:
            self.add(DashedLine(ax.c2p(model.HANDOFF,ax.y_range[0]),ax.c2p(model.HANDOFF,ax.y_range[1]),color=MUTED,stroke_width=1.6,dash_length=.08))
            self.add(plot(ax,fn,0,model.HANDOFF,ORANGE),plot(ax,fn,model.HANDOFF,model.END,TEAL))
            self.add(Dot(ax.c2p(model.HANDOFF,fn(model.HANDOFF)),radius=.065,color=INK))
        self.add(text('Switch at T = 1.25',22).move_to([0,-2.83,0]))
        self.add(text('V(0) = %.3f   →   V(T) = %.3f'%(model.energy(model.Z0),model.energy(model.ZT)),25).move_to([0,-3.31,0]))
        self.add(text('The handoff is not rest: v(T) = %.3f, a(T) = %.3f.  The all-box guarantee comes from the separate proof.'%(model.ZT[1],model.ZT[2]),19,MUTED).move_to([0,-3.84,0]))
