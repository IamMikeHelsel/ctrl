import json,datetime
from pathlib import Path
B=Path(__file__).resolve().parent
cards=[]
def card(id,title,status,deliverable,barrier,diagnostic,gate,publication,sources,priority):
    cards.append(dict(id=id,title=title,status_verified_2026_10_17=status,priority=priority,budget_seconds=300,
      run_mode='local/read-only discovery; no accounts, submissions, network services or paid computation',
      useful_smaller_deliverable=deliverable,prerequisite_barrier=barrier,
      diagnostic_task=diagnostic,success_artifact='result.json containing exact statement/inputs, source revision and hashes, commands, output, proof/checker status, negative results, remaining bridge and elapsed seconds',
      decision_gate=gate,publication_and_novelty_limit=publication,primary_sources=sources,
      forbidden_inferences=['A timeout or no route found does not imply impossibility.','Finite tests are not a universal conjecture proof.','A local pass is not competition acceptance, novelty, payout or publication acceptance.']))
card('clay-bsd','Birch and Swinnerton-Dyer','Clay: Unsolved',
 'A reusable exact finite-field point-count certificate, starting with E: y^2=x^3-x and the known trace-zero identity at primes p=3 mod 4.',
 'General BSD needs rational Mordell-Weil rank, analytic continuation and leading L-values; point counts alone do not bridge those obligations.',
 'Pin the existing elliptic-curve/finite-field API; for primes 3<=p<200 with p mod 4=3, count affine solutions plus infinity exactly and test #E(F_p)=p+1. Write the x -> -x/Legendre-symbol cancellation argument and isolate any missing theorem; do not treat finite enumeration as that proof.',
 'Continue if a short universal finite-field lemma is absent/useful and independently matches point counts; otherwise reuse the library and choose a genuinely missing arithmetic-certificate interface.',
 'This CM identity is classical. New value would require a reusable verified arithmetic interface or a novel mathematical result, not rediscovery of the identity.',
 ['https://www.claymath.org/millennium/birch-and-swinnerton-dyer-conjecture/'],7)
card('clay-hodge','Hodge conjecture','Clay: Unsolved',
 'A precise cycle/intersection certificate for the two factor curves and diagonal on E x E, followed by a checked geometric interpretation.',
 'The rational Hodge conjecture requires cycle classes, cohomology and Hodge decomposition. An intersection matrix does not prove these classes span every rational (1,1) class; non-CM assumptions matter.',
 'Check the exact candidate intersection matrix [[0,1,1],[1,0,1],[1,1,0]] has determinant 2 and signature (1,2), while separately inventorying cycle-class and product-cohomology APIs. Record every geometric assumption required to identify it with E x E.',
 'Advance only if the geometry-to-algebra bridge has a named source and feasible formal prerequisites; stop at the matrix lemma otherwise.',
 'The example is known. A generic formal intersection/cycle framework could be useful; a 3x3 determinant alone is not publishable Hodge progress.',
 ['https://www.claymath.org/millennium/hodge-conjecture/'],11)
card('clay-pnp','P versus NP','Clay: Unsolved',
 'A small proof-complexity artifact: certified resolution traces and exact minimum-refutation diagnostics for a fixed pigeonhole CNF family.',
 'Finite SAT/UNSAT certificates and resolution lower bounds for a restricted proof system do not separate P from NP. A universal complexity claim needs an explicit machine model and all input lengths.',
 'Encode PHP(3,2), enumerate assignments to validate unsatisfiability, and replay one resolution certificate using existing Lean SAT/LRAT infrastructure if already installed. If absent, emit a precise checker lemma obligation and do not install a large solver stack during the slot.',
 'Continue only toward a missing universal checker/complexity lemma or a demonstrably new restricted-family result; do not extend brute-force enumeration as a P-vs-NP strategy.',
 'Ordinary PHP unsatisfiability and resolution lower bounds are established. A substantial verified proof-complexity development might support publication; the tiny instance is a pipeline test.',
 ['https://www.claymath.org/millennium/p-vs-np/'],8)
card('clay-rh','Riemann hypothesis','Clay: Unsolved',
 'A certified interval/checker bridge for a stated finite-height zero-count or explicit prime-counting bound, with the analytic remainder obligation stated separately.',
 'Floating-point zero plots do not exclude off-line zeros. Rigorous interval bounds and a completeness/counting argument such as Turing-method machinery are required; the universal height limit remains.',
 'First locate and pin a primary finite-height verification theorem and its exact error lemma. Test one rational interval subclaim against an installed interval library. If no certified arithmetic API is available, report that dependency rather than producing ordinary floating-point evidence.',
 'Continue only if one explicit analytic remainder/checker gap can be stated and tested. Do not claim a finite-height test proves RH or improves the published height.',
 'Established explicit formulas and low-height checks are not novel. A reusable formal analytic certificate or new verified bound needs specialist comparison.',
 ['https://www.claymath.org/millennium/riemann-hypothesis/'],10)
card('clay-yang-mills','Yang-Mills existence and mass gap','Clay: Unsolved',
 'A verified spectral-gap certificate for a specified finite-dimensional self-adjoint truncation, with a separate continuum-transfer obligation.',
 'A positive matrix eigenvalue gap is not a continuum quantum-field mass gap. Gauge constraints, continuum/infinite-volume limits and the quantum-field axioms are the hard missing bridge.',
 'Select a supplied exact rational symmetric truncation and prove/check H-lambda*I is PSD on a stated subspace using LDL witnesses; report dimension, subspace and lambda. If no physically sourced operator is supplied, perform only a library/interface inventory, not an invented physics example.',
 'Continue only if a domain expert supplies a meaningful truncation and a named controlled-limit argument; otherwise retain as general spectral-certificate tooling.',
 'LDL positivity is known and our controls pipeline already handles it. Publication requires a substantive new quantum application/limit theorem, not renaming a matrix certificate.',
 ['https://www.claymath.org/millennium/yang-mills-the-maths-gap/'],12)
card('clay-navier-stokes','Navier-Stokes existence and smoothness','Clay: Active; apparent resolution announced September 11, evaluation pending',
 'A rigorously checked nonlinear energy-cancellation lemma for a specified divergence-free Fourier-Galerkin truncation, or one precisely identified lemma in the announced proof after obtaining that source.',
 'Finite ODE/Galerkin bounds need uniform estimates and compactness/limit control for the PDE. Our finite actuator proof does not supply these. The announced resolution must be inspected rather than presumed accepted.',
 'Pin the official Clay announcement and a supplied mathematical paper. For an explicitly specified finite Fourier mode set, check exact triad skew-symmetry and energy cancellation with rational coefficients; list the PDE limit lemma that remains. If paper/operator data are absent, return that missing input.',
 'Advance a missing reusable PDE lemma or independent proof audit, not an ungrounded claim to be the first solution. A failed tiny diagnostic is not evidence against the PDE theorem.',
 'Energy cancellation is classical. A substantial machine-checked PDE bridge or useful independent audit may be publishable; a finite symbolic check alone is not.',
 ['https://www.claymath.org/millennium/navier-stokes-equation/','https://www.claymath.org/news/navier-stokes-announcement/'],9)
card('beal','Beal conjecture','Advertised $1M; current administrator award availability not reconfirmed',
 'A verified modular-obstruction certificate for one explicitly bounded exponent/residue family, with a reusable residue-cover checker.',
 'The conjecture ranges over all positive bases and all exponents >2. gcd(A,B,C)=1 is the primitive-counterexample condition, not a warrant to silently narrow the search to pairwise coprime bases without proof.',
 'For a preselected exponent triple, e.g. (3,4,5), compute exact residue sets modulo a short fixed prime list and identify which primitive residue classes are excluded. Emit modular witnesses and any surviving classes. Do not report a finite base search as a proof.',
 'Continue if a complete symbolic family cover or a genuinely new reduction emerges; stop expanding a blind search merely because it found no counterexample.',
 'Modular sieving and many generalized Fermat signatures are heavily studied. Any new bound must be checked against that literature; checker tooling may be useful but is not a Beal solution.',
 ['https://www.bealconjecture.com/','https://www.ams.org/profession/prizes-awards/ams-supported/beal-prize-rules'],6)
card('collatz','Collatz','Sponsor advertises JPY120M; conditional terms through July 6, 2031',
 'An exact affine parity-word certificate and a theorem covering one stated family of positive starting values.',
 'A finite stopping-time table does not exclude divergent orbits or unknown cycles. An accelerated map must be explicitly related to the standard Collatz map.',
 'Use T(n)=n/2 for even n and (3n+1)/2 for odd n. For parity words of fixed length k<=12, derive T^k(n)=(3^s*n+b)/2^k on its residue class, and test the exact descent inequality with its threshold. Report all uncovered classes and the induction obligation.',
 'Continue only if a new covering/induction mechanism covers a strictly larger infinite family without an unproved termination hypothesis; otherwise retain a reusable verifier and stop brute-force scaling.',
 'Parity-vector affine formulas and finite sieves are known. Novelty requires a new structural theorem; more verified starting values alone are not a credible near-term prize route.',
 ['https://mathprize.net/posts/collatz-conjecture/','https://mathprize.net/files/collatz-conjecture-rule-en-20210707.pdf'],5)
card('proximity','Proximity / Better Codes','Program active to Dec 31, 2027 under current terms; companion leaderboard has separate rules',
 'Parameterize the existing upper-bound fibre/pigeonhole construction and test one improved count of attainable coefficient/product signatures.',
 'Existing score rounding and simple powers-of-two parameter sweep are already exhausted locally. A new bound needs a mathematical counting improvement, plus the pinned Lean 4.32.2/ArkLib/CompPoly environment.',
 'Reuse pinned ed2b68c4a330d76dc4ab6693eec81b685b493270. For exactly one stated refined signature relation, derive an exact integer cardinality bound and compare it with the frozen 512-fibre/272-selected inequality. Reject any refinement that silently assumes independent coefficients or changes the protected target.',
 'Proceed only with a strict exact inequality improvement or a reusable parameterized theorem. If no improved relation is found after bounded development, stop the refinement; no record is implied by a replay.',
 'A new counting theorem or broadly reusable formal construction could be a paper. The existing proof and our negative parameter checks are not a new record or award claim.',
 ['https://proximityprize.org/terms/','https://github.com/proximity-prize/proximity-prize/tree/ed2b68c4a330d76dc4ab6693eec81b685b493270','https://better.codes/'],3)
card('sair-kernel-permanent','SAIR Lean Kernel: sparse permanent','Stage 1 cutoff November 20, 2026; cash amount unverified',
 'A total sparse-row implementation with universal correctness against permanentSpecN, then the official local evaluator compared on identical cases/spec.',
 'The official target takes a packed Nat encoding dimension and seed and generates a particular matrix family; the entry theorem is not an arbitrary-input-matrix interface. Official ranking uses Linux instruction counts, not Python timings or local process time.',
 'Replay kernel-spike/Submission.lean under Lean 4.33.1, verify the locked Spec hash, audit impl_correct, then run one complete official local public-plan comparison against the supplied baseline if dependencies are preprovisioned. If five minutes expires, record incomplete cases and no total.',
 'Proceed if every case passes and the gain survives matched canonical kernel replay. Then compare current published competitors and try a second general representation improvement; never hardcode answers.',
 'Sparse matrices are classical; this small change alone is unlikely to be a paper. A general kernel-computation optimization framework with rigorous comparisons may be. Local improvement is not leaderboard novelty.',
 ['https://github.com/SAIRcompetition/lean-kernel-challenge/tree/940f0a2ead23ef70ab1387edabb347e629111edd','https://github.com/SAIRcompetition/lean-kernel-challenge/blob/940f0a2ead23ef70ab1387edabb347e629111edd/rules/problems/permanent.md'],1)
card('sair-andrews-curtis','SAIR Andrews-Curtis: exact move certificates','Discovery/Proof tracks open; November 30, 2026 deadline; cash amount unverified',
 'A certificate-producing bounded path search plus exact replay, initially for a short official rank-two presentation.',
 'A verified path solves one presentation, not the general conjecture. The leaderboard rewards the shortest current paths; an easy existing solution may earn nothing. Stable AC has a separate rank<=8 contest restriction.',
 'Replay ac-local-certificate.txt for ac-08491 against pinned a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e; verify each move with the reference CLI, then independently implement free-word replay. Spend any remaining time checking a shorter path under an explicitly bounded search, keeping unknown global shortest status.',
 'Continue only if a route improves a currently published record or yields a reusable family theorem/checker. Obtain standings before any novelty or competition-value claim.',
 'One eight-move example is unlikely novel. A general shortening method, verified family result or proof-producing search tool may support publication after related-work comparison.',
 ['https://github.com/SAIRcompetition/Andrews-Curtis/tree/a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e','https://github.com/SAIRcompetition/Andrews-Curtis/blob/a0fd6e6f52d82c93ccc06ab91d81e8fa3678256e/competition/rules/discovery.md'],2)
card('sair-inverse-galois','SAIR Inverse Galois','IGP24 June-August round finished; fall Stage 2 announced but concrete new rules not verified',
 'An explicit degree-24 polynomial certificate package: irreducibility, real-root signature, factorization evidence and correctly distinguished polynomial/field discriminants.',
 'Finite-prime factorization patterns constrain but need not identify a Galois group. Full identification uses more group/resolvent machinery; polynomial discriminant can differ by an index square from the field discriminant. Magma access may be a prerequisite.',
 'Pin a single published example polynomial and old-round evaluator. Recompute exact discriminant and Sturm real-root count using already installed algebra tools, then identify the missing group certificate. First recheck whether new Stage 2 rules have been published; do not reuse expired entry terms as current.',
 'Proceed only with a stated missing group/signature target, live rules if competition participation is intended, and reproducible group identification. Do not spend a slot on licensed-tool installation.',
 'New small-discriminant fields or a reusable independently checkable group-certificate bridge can be meaningful. Replaying a known polynomial is setup, not a new realization.',
 ['https://github.com/SAIRcompetition/IGP24-public/blob/main/competition/rules/overview.md','https://competition.sair.foundation/competitions/igp24/evaluation-setup','https://blog.sair.foundation/an-open-commitment-to-mathematics-and-science/'],4)
out={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'queue_version':1,
'scope':'All five Clay unsolved plus active Navier-Stokes; Beal; Collatz; Proximity; three SAIR tracks. No solve probabilities.',
'preflight':'Before the 300-second task timer, provision the pinned runtime, source and checker. Five minutes is a diagnostic budget, not time spent downloading packages. Use one CPU process for matched timings; no GPU needed for these exact probes. A local language model is optional and must not be treated as a checker.',
'tasks':cards}
(B/'task-cards.json').write_text(json.dumps(out,indent=2)+'\n')
print(len(cards),'cards written')
