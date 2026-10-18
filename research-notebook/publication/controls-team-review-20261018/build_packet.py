from pathlib import Path
from xml.sax.saxutils import escape
import json
import reportlab
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib import colors
from reportlab.lib.styles import ParagraphStyle
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak
from reportlab.graphics.shapes import Drawing, Rect, String, Line, Circle

ROOT = Path(__file__).resolve().parent
fonts = Path(reportlab.__file__).parent/'fonts'
pdfmetrics.registerFont(TTFont('Vera', str(fonts/'Vera.ttf')))
pdfmetrics.registerFont(TTFont('VeraBold', str(fonts/'VeraBd.ttf')))
pdfmetrics.registerFontFamily('Vera',normal='Vera',bold='VeraBold',italic='Vera',boldItalic='VeraBold')
navy=colors.HexColor('#163243');teal=colors.HexColor('#007F82');pale=colors.HexColor('#EAF4F3')
body=ParagraphStyle('Body',fontName='Vera',fontSize=10,leading=14,textColor=navy,spaceAfter=8)
small=ParagraphStyle('Small',parent=body,fontSize=8.5,leading=11.6,spaceAfter=6)
heading=ParagraphStyle('Heading',parent=body,fontName='VeraBold',fontSize=15,leading=19,spaceBefore=10,spaceAfter=9)
title=ParagraphStyle('Title',parent=heading,fontSize=25,leading=30,spaceAfter=14)
mono=ParagraphStyle('Math',parent=body,fontName='Courier',fontSize=9.1,leading=13,backColor=pale,borderPadding=8,spaceBefore=5,spaceAfter=13)
story=[]
def p(text,style=body):story.append(Paragraph(text,style))
def h(text):p(text,heading)
def page(label,title_text):
 if story:story.append(PageBreak())
 p(label.upper(),small);p(title_text,title)
def table(rows,widths):
 t=Table([[Paragraph(escape(str(c)),small) for c in row] for row in rows],colWidths=widths,hAlign='LEFT')
 t.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),pale),('VALIGN',(0,0),(-1,-1),'TOP'),('LEFTPADDING',(0,0),(-1,-1),8),('RIGHTPADDING',(0,0),(-1,-1),8),('TOPPADDING',(0,0),(-1,-1),7),('BOTTOMPADDING',(0,0),(-1,-1),7),('LINEBELOW',(0,0),(-1,-1),.4,colors.HexColor('#C8D6DC'))]))
 story.extend([t,Spacer(1,10)])

page('Team review / 18 October 2026','A travel bound we can inspect')
p('<b>Review owner: Mike Helsel.</b> Prepared with AI assistance. Private review packet; nothing has been sent to a team or submitted.')
p('<b>Decision requested:</b> Is the sampled-control proof useful enough to develop as a formal-methods case study or reusable Lean component? The existing theorem is ready for technical review. Publication novelty is not established.')
h('The practical question')
p('When a digital controller updates an actuator, can the axis cross its position limit before the next update? Our original controls result gives an all-time position bound for one declared actuator model. It includes clipping, uncertain fixed lag, irregular sampling and bounded errors held between samples.')
diagram=Drawing(520,101)
labels=[['Own sampled state','and held command'],['Exact actuator flow','and 12 certificates'],['All-time invariant','and execution proof'],['Position envelope','including between updates']]
for i,lines in enumerate(labels):
 x=i*131;diagram.add(Rect(x,27,123,68,rx=6,ry=6,fillColor=pale,strokeColor=teal,strokeWidth=.7))
 for j,line in enumerate(lines):diagram.add(String(x+61.5,69-j*15,line,fontName='Vera',fontSize=7.4,textAnchor='middle',fillColor=navy))
 if i<3:diagram.add(Line(x+123,60,x+130,60,strokeColor=teal,strokeWidth=1.3))
diagram.add(String(0,6,'Proof structure, not a simulated trajectory.',fontName='Vera',fontSize=8,fillColor=navy));story.append(diagram)
h('Two results, with different assumptions')
table([['Result','What is checked','Review position'],['A. Sampled travel envelope','Fixed uncertain lag; saturated sampled feedback; held errors; safety for every nonnegative time; existence and uniqueness.','Primary controls review candidate. Six-page paper and frozen replay exist.'],['B. Changing-response settling','Continuous feedback; bounded time-varying response and disturbance; one supplied trajectory and initial error cube.','Later extension. Tracking and hold are composed without resetting state.']], [130,235,163])
p('<b>Do not combine their assumptions.</b> Result B does not add time-varying lag to Result A, and Result A does not add sampled feedback or clipping to Result B.')
p('The robot-motion paper includes Result B. Result A remains a separate paper. Keeping this distinction is essential to a fair review.',small)

page('Result A / the original controls solution','Safety between updates')
p('Normalized state z=(x,v,a), command k(z)=-x-3v-2a. At sample n, the controller reads its own trajectory and holds the resulting command until the next sample.')
p("x' = v;  v' = a;  a' = r(u_n-a)<br/>u_n = clip[-1,1](k(z(t_n)) + e_n) + d_n",mono)
table([['Required condition','Meaning'],['r in [0.9,1.1], fixed for the execution','Unknown actuator rate. It does not change during this theorem.'],['0 < h_min <= h_n <= 0.2','A uniform positive lower bound prevents infinitely many updates in finite time.'],['|e_n| + |d_n| <= 0.01','Combined error budget; both values are held during each interval. Post-clamp error is inside the rate multiplier.'],['z_0^T P z_0 <= 12','Initial position, velocity and acceleration must satisfy one coupled condition. Position alone is insufficient.']], [210,318])
p('P = [[38/5, 257/25, 5],<br/>&nbsp;&nbsp;&nbsp;&nbsp; [257/25, 1319/50, 769/50],<br/>&nbsp;&nbsp;&nbsp;&nbsp; [5, 769/50, 278/25]]',mono)
p('<b>Conclusion:</b> An execution exists. It is unique for the same prescribed sampling and error sequences. Every execution satisfying the ODE has z(t)<super>T</super>Pz(t) &lt;= 12 and |x(t)| &lt;= 2 for every t &gt;= 0, including between updates.')
h('An illustrative physical scale')
p('Nominal lag 0.1 s and clamp command limit 2 m/s² give an axis position envelope of ±4 cm, sample intervals at most 20 ms, combined held error at most 0.02 m/s², and a fixed actual lag between about 90.91 and 111.11 ms. These are assumed values, not robot measurements. The initial ellipsoid still applies.')
p('<b>Useful negative checks:</b> Active clipping is admitted. A state already inside the position interval can still escape if the initial ellipsoid is omitted. Replacing the middle Bernstein coefficient with the midpoint plant, or dropping the rate multiplier from the ODE, breaks the checked model link.',small)
p('This is position relative to an origin, not accumulated travel distance, collision avoidance, or an emergency-stop guarantee. The total drive can exceed the clamp limit because the second error enters after clipping.',small)

page('Result B / overnight progress','A hold that inherits the motion')
p('The later result carries the same scalar physical trajectory through a return and final hold. It shifts the state, response and disturbance clocks together. It does not assume a new safe state at the handoff.')
p("x'=v; v'=a; a'=r(t)(u+w-a)<br/>u=q''-800(x-q)-60(v-q')-(a-q'')/2+q'''/96",mono)
p("Here q is reference position; e_x=x-q, e_v=v-q', and e_a=a-q''.")
p('Conditions: 80 &lt;= r(t) &lt;= 120 per second and |w(t)| &lt;= 0.01 m/s². A classical trajectory on [0,H], H &gt;= 3.42 s, is supplied. At time zero, the absolute values of e_x, e_x+e_v/40 and e_x+e_v/20+e_a/1600 are each at most 0.0002 m. These are coupled error coordinates.')
p('The reference is a four-box finite impulse response (FIR) history with width 0.2 s, a +20 mm event at 0.22 s and a -20 mm event at 0.62 s. The response and disturbance may change within their bounds; no response derivative or dwell-time bound is required.')
line=Drawing(520,108)
line.add(Line(18,60,506,60,strokeColor=teal,strokeWidth=3))
for x,label,desc in [(18,'0','One initial cube'),(214,'1.42 s','Position within 0.2 mm'),(402,'3.42 s','Speed / acceleration bands'),(506,'H','End of supplied interval')]:
 line.add(Circle(x,60,4,fillColor=teal,strokeColor=teal));line.add(String(x,81,label,fontName='VeraBold',fontSize=10,textAnchor='middle',fillColor=navy))
line.add(String(18,30,'State continues through the handoff. Schematic; H may equal 3.42 s.',fontName='Vera',fontSize=9,fillColor=navy));story.append(line)
p('<b>Conclusion:</b> Tracking position error is at most 0.2 mm throughout [0,H]. The axis advances at least 1 mm by 0.5 s. Position is within 0.2 mm of the zero goal from 1.42 s through H. Speed is at most 1 mm/s and acceleration at most 0.02 m/s² from 3.42 s through H.')
h('What was closed, and what remains open')
p('The tracking and terminal-hold proofs now share one physical trajectory and one initial condition. An independent witness satisfies the premises but has nonzero speed at 3.42 s. Exact finite-time rest cannot be inferred.')
p('This theorem assumes a classical solution; it does not prove existence for every arbitrary bounded signal pair. It does not cover sampled feedback, clipping, delay, coupling, contact or loss of grip outside the response band. It does not prove the 1.70 s numerical terminal task.')
p('Physical application remains conditional on measured model bounds and implementation correspondence. Neither result establishes a Franka, PL d/e, or hardware safety claim.',small)

page('Novelty / targeted assessment','What might be worth publishing?')
p('<b>Assessment:</b> The defensible candidate is a reusable formal application and proof-composition case study. A new control method, a first Lean stability result, and a superior verification pipeline are not established.')
rows=[['Closest work','Known overlap','Question for our contribution'],['Doll & Shames [1]','Lean Lyapunov and small-gain foundations; general stability abstractions.','Does our sampled ODE/execution bridge fill a useful API gap or duplicate an existing abstraction?'],['Hellwig et al. [2]','Formal control envelopes with one-step invariance, intersample safety and admissible controls.','Does our exact lag/clipping/error case add useful Lean integration or a distinct benchmark? No matched advantage is shown.'],['Arechiga et al. [3]','Theorem-prover conditions for closed-loop controllers, including sampled/networked execution.','Is the own-sample-state execution contract a useful mechanization detail rather than a new concept?'],['Lean SOS [4] and LeanCert [5]','Existing nonlinear certificate tooling; LeanCert documents exact scalar Bernstein bounds and trust modes.','Can existing tooling replace or support our matrix certificate layer? No generic checker-priority claim.']]
table(rows,[134,184,210])
h('Best candidates for Lean review')
p('<b>1. Reusable certificate interface.</b> Matrix Bernstein positivity and rational LDL checks, with a separate proof that the finite data describe the ODE. Test reuse on a genuinely different model; rescaling the current axis is not sufficient.')
p('<b>2. Execution bridge.</b> Existence, uniqueness and safety for any continuous trajectory satisfying its own sampled-feedback ODE. Ask whether the interface composes cleanly with the current Lean control library.')
p('<b>3. Time-scaled robustness.</b> The elapsed-time factor avoids a fixed error penalty at tiny sample durations. The mathematics is established; judge the generic lemma and its reuse value.')
p('The changing-response hold result is a related follow-on, not an automatic stronger version of the sampled theorem. Keep it as a clearly marked companion until a shared implementation model is proved.',small)
p('This is a targeted primary-source comparison, not an exhaustive novelty search, external peer review, or an absence proof. Broader repository README claims are not evidence of novelty.',small)

page('Review plan / evidence / sources','A concrete team decision')
table([['Role / time','Review task','Required output'],['Controls reviewer / 20 min','Challenge the plant, initial set, error placement and fixed-rate limit. Name one actual task with measured bounds.','Useful application, required model change, or reject as too specialized.'],['Lean reviewer / 20 min','Inspect the theorem statements and reusable modules. Compare with [1], [4], [5]. Replay the frozen artifact.','Specific reuse/overlap finding and accept/repair decision; compilation is not novelty.'],['Joint review / 15 min','Select one next test and a publication type.','Proceed with a reusable component/case study, request one experiment, or stop.']], [132,260,136])
p('<b>Proof entry points:</b> Result A: LeanControls.ExecutionUniqueness.execution_travel_limit and LeanControls.PhysicalExecutionUniqueness.execution_travel_limit. Result B: RobotMotion.FIRHold.delayed_return_physical_terminal. See READ-ME.txt and NOVELTY-EVAL.txt for source paths, replay commands and acceptance criteria.',small)
p('<b>Evidence boundary:</b> A prior fresh-source replay of Result A passed 63 modules and audited 830 public declarations. Its five-step project check also covers regeneration and model mutations. Result B passed its independent 54-module review and is included in the accepted V4 package. These are different proof sets; their counts must not be added as contributions. This packet rechecks hashes and exact numerical translations, not a new whole-project proof build.',small)
h('Primary sources checked for this review')
sources=[('[1] Doll & Shames. Foundations of Machine-Checked Control Theory in Lean (2026).','https://arxiv.org/html/2607.19727v1'),('[2] Hellwig et al. From Zonotopes to Proof Certificates (2025 preprint).','https://arxiv.org/html/2509.20301v1'),('[3] Arechiga et al. Using Theorem Provers to Guarantee Closed-Loop System Properties (ACC 2012).','https://logic.kastel.kit.edu/ap/pub/TPgenloop.pdf'),('[4] Lean SOS. Nonlinear real-arithmetic certificate tooling.','https://github.com/leanprover/sos'),('[5] LeanCert. Tactics reference, Bernstein bounds and verification routes.','https://docs.leancert.io/reference/tactics/')]
for label,url in sources:p(escape(label)+'<br/><link href="'+url+'" color="#007F82">'+escape(url)+'</link>',small)
p('Release gate: human novelty/value judgment, affiliation and release approval, license and venue. The historical six-page manuscript remains unchanged. Its author placeholder and bibliography metadata must be checked before submission. No team message or external submission was sent.',small)

def footer(canvas,doc):
 canvas.setStrokeColor(teal);canvas.line(42,35,570,35);canvas.setFillColor(navy);canvas.setFont('Vera',8)
 canvas.drawString(42,23,'CONTROLS REVIEW | PRIVATE DRAFT | 18 OCT 2026');canvas.drawRightString(570,23,str(doc.page))
path=ROOT/'output/pdf/controls-review-brief.pdf'
SimpleDocTemplate(str(path),pagesize=(612,792),rightMargin=42,leftMargin=42,topMargin=38,bottomMargin=47,title='A travel bound we can inspect - controls team review',author='Prepared for Mike Helsel with AI assistance').build(story,onFirstPage=footer,onLaterPages=footer)
print(path)
