// Complete states permit direct jumps, reverse traversal, and timed playback.
const box=(id,label,x,y,w=250,h=90,color='ink')=>({id,type:'box',label,x,y,w,h,color});
const note=(id,label,x,y,w=360,h=75)=>({id,type:'note',label,x,y,w,h,fontSize:25});
const label=(id,label,x,y,color='ink',fontSize=27)=>({id,type:'label',label,x,y,color,fontSize});
const arrow=(id,points,label='',color='ink')=>({id,type:'arrow',points,label,color});
const step=(title,caption,show,focus=[])=>({title,caption,show,focus,durationMs:5500});

export function storiesFrom(report){
 const data=Object.fromEntries(report.experiments.map(e=>[e.id,e]));
 const source_derivation={id:'math-explainers-144',sha256:report.sha256};
 const witness=data.saturation.witness;
 return [
 {id:'proof-dependencies',title:'What connects a proof to a robot?',category:'Dependencies / Tao Blueprint inspiration',seed:144,source_derivation,
 summary:'Make the checked layers and the missing bridges visible.',
 items:[box('model','Stated model',65,170),box('math','Mathematical proof',430,170),box('code','Executable behavior',795,170),
 arrow('a',[[325,215],[418,215]]),arrow('b',[[690,215],[783,215]],'refinement','orange'),
 box('timing','Timing + actuation',795,385,250,90,'orange'),arrow('c',[[920,272],[920,373]],'','orange'),
 box('plant','Physical bounds',430,385,250,90,'orange'),arrow('d',[[783,430],[692,430]],'','orange'),
 note('scope','A checked claim has a boundary.',65,390,310,90),label('legend','Green: checked statement   ·   Orange: separate obligation',560,550,'muted',25)],
 steps:[step('Start with a statement','A theorem has explicit hypotheses and a precise conclusion.',['model']),
 step('Check the mathematical implication','Lean checks a proof of that statement. SymPy and finite tests provide other kinds of evidence.',['model','math','a']),
 step('Connect the executable','A declaration-name link alone does not prove the implementation refines the model.',['model','math','a','code','b'],['code','b']),
 step('Expose the remaining dependencies','Timing, command application and physical bounds need their own evidence. This drawing is a dependency map inspired by Tao’s Blueprint presentation, not a claim that those bridges are proved.',['model','math','a','code','b','timing','c','plant','d','scope'])]},
 {id:'saturation-order',title:'Can these operations be regrouped?',category:'Algebra / finite countermodel',seed:145,source_derivation,
 summary:data.saturation.conclusion,
 items:[label('rule',`clip to [−${witness.bound}, ${witness.bound}] after each addition`,560,145),box('inputs',`a=${witness.a}, b=${witness.b}, c=${witness.c}`,360,190,400),
 arrow('l',[[470,290],[280,345]]),arrow('r',[[650,290],[840,345]]),box('left',`clip(clip(a+b)+c) = ${witness.left}`,80,365,430),box('right',`clip(a+clip(b+c)) = ${witness.right}`,610,365,430),note('lesson','Same inputs. Different applied command.',280,505,560)],
 steps:[step('State the operator','This operator adds two numbers and clips the result.',['rule']),step('Freeze one input triple','A finite counterexample is enough to reject a universal reassociation rule.',['rule','inputs']),step('Evaluate both groupings','Each branch clips after its first addition. The result depends on grouping.',['rule','inputs','l','r','left','right']),step('Keep the operation order','The search method is inspired by Tao’s equational-theories project. This is our small control-operator experiment.',['rule','inputs','l','r','left','right','lesson'])]},
 {id:'schedule-bound',title:'A lower bound is not a schedule',category:'Scheduling / OpenAI math inspiration',seed:146,source_derivation,
 summary:data.scheduling.conclusion,
 items:[box('first','Four source jobs',100,190,340),box('second','Four dependent jobs',680,190,340),arrow('precedence',[[452,235],[668,235]],'every source first'),
 label('work','8 jobs / 3 machines → at least 3 slots',560,355,'blue'),label('layer','Each four-job layer needs at least 2 slots',560,420,'green'),note('sum','2 + 2 = 4 slots. The layers cannot overlap.',230,500,660)],
 steps:[step('Freeze the scheduling model','Unit-duration jobs, three identical machines, no release times or transport costs.',['first','second']),step('Add precedence','Every source job must finish before any dependent job starts.',['first','second','precedence']),step('Try the elementary bound','The workload bound gives 3 slots; the critical-path bound gives 2. Their maximum is still only a lower bound.',['first','second','precedence','work']),step('Find the missing obstruction','The two layers require at least 4 slots in total, and a feasible four-slot schedule attains it. This tiny oracle is not OpenAI’s scheduling algorithm.',['first','second','precedence','work','layer','sum'])]},
 {id:'reachable-holes',title:'An interval can hide unreachable states',category:'Reachability / sumset experiment',seed:147,source_derivation,
 summary:data.sumsets.conclusion,
 items:[box('increments','Each increment: −3 or +3',310,145,500),arrow('time',[[560,245],[560,305]],'three additive steps'),label('states','Reachable: {−9, −3, 3, 9}',560,355,'green',33),box('hull','Integer interval hull: −9 through 9',155,415,810),note('holes','4 reachable points · 19 points in the hull',240,530,640,65)],
 steps:[step('Keep the discrete support','Each of three independent increments belongs to the two-point set {−3, 3}.',['increments']),step('Compose with set addition','Enumerate sums, or compute the iterated sumset.',['increments','time']),step('Compare to an interval','The interval is a sound outer approximation, but includes points this exact model cannot reach.',['increments','time','states','hull']),step('Measure the tradeoff','The sumset viewpoint is inspired by Green, Manners and Tao. A real compression scheme still needs inclusion and cost checks.',['increments','time','states','hull','holes'])]}
 ];
}
