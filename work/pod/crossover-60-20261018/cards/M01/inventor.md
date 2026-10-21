# M01 cross-discipline inventor

AI-written research; inherited root model, exact model identifier unavailable. Root owns elapsed-time accounting and the PM decision. This role changed only its own `inventor*` files. No original 885 source, approved challenge, live search, or remote resource was changed.

## Question and recovered evidence

Extend the saved rational 6-by-4 square-sum grid by one fifth distinct column. In the first saved class the five nonzero row parameters are

    N = [206222625, 677376000, 2019635200, 4786481700, 16670745700]
    known positive w = [13440, 75936, 129360, 279840].

The exact obligation is a positive rational w, distinct from those four, such that every w²+4N_i is a rational square. Negative w repeats the same squared column. The sixth row is the automatic zero-row square w².

Sources inspected: `/Users/mike/Dev/ctrl/work/pod/885/FINDINGS.md`, `/Users/mike/Dev/ctrl/work/pod/885/extend_6x4.py`, campaign charter and frozen M01 card. Current FINDINGS reports bounded q≤10^6 negatives for two classes and corrects an earlier rediscovery claim. Those are source reports, not fresh execution or a novelty assessment by this role. All experiments below concern the first class only. No denominator scan was repeated.

## Three transfers and their falsifiers

**1. Distance localization and cycle consistency.** Map each row-column entry to a squared distance label z_i²=w²+4N_i. Differences between row labels must equal the fixed 4(N_i−N_j); four-cycle sums of the corresponding rectangular array vanish. This preserves additive consistency and can expose a corrupted grid or incorrect coordinate conversion. It does not preserve rational realizability: for every positive real w, all these roots exist over the reals. Even rational w with nonsquare factors passes the cycle identities. The falsifier is an exact candidate satisfying all cycles while failing an individual rational-square test; the doubled elliptic point below supplies one. **NO-GO as a new arithmetic discriminator by itself.** Useful only as a representation audit. The lesson transferred back to localization is that redundant consistency equations can conceal the actual domain constraint.

**2. Elliptic quotient with explicit lift obligations.** Set X=w², A_i=4N_i and use

    E: Y²=(X+A_1)(X+A_2)(X+A_3).

A complete column maps to E by multiplying the first three roots. The converse requires X>0, X a rational square, all five X+A_i rational squares, and a distinct w. Those obligations are retained separately. Exact rational chord operations generate structured candidates from the saved columns without scanning denominators. An elementary polynomial identity explains a useful partial preservation: for a chord/tangent line ℓ through lifted P,Q and third intersection R,

    f(X)−ℓ(X)²=(X−x_P)(X−x_Q)(X−x_R),
    x_R+A_i = [ℓ(−A_i)/(s_Pi s_Qi)]²,  i=1,2,3.

The denominator must be nonzero; torsion inputs can violate that premise. Thus ordinary sums of supplied lifted points automatically preserve the three quotient square factors. Checking those again is a certificate check, not three fresh discoveries. The substantive remaining conditions are the square coordinate X and rows four and five. The falsifier for any curve-only claim is 2P1 below; torsion translates are a second negative control for assuming all quotient points lift. This role did not invoke a complete descent, compute the Mordell–Weil group, or prove that the known points generate it.

**3. Unexpected transfer: error-detecting codes on finite group states.** Treat the six square-class obligations as parity checks after reduction at a good odd prime. Their checks are correlated; duplicate shift residues are recorded rather than counted as independent evidence. Instead of evaluating huge rational group expressions and checking them afterward, compute a necessary coefficient-state condition in E(F_p). Invalid residue states reject entire coefficient classes cheaply. The preserved implication is rational-square necessity after reduction, with projective infinity retained when denominators contain p. The general coefficient inference also uses the good-reduction group homomorphism; our finite enumeration is exact computational evidence, not a Lean proof of that theorem. A falsifier is any valid saved column rejected by the code, any rational operation disagreeing with the reduced operation, or an omitted infinity branch. Passing the code cannot certify rational square roots, positivity, distinctness, or global completeness.

## Exact tests and outcomes

`inventor_elliptic.py` performs 32 declared operations: pairwise sums/differences of the four positive-Y lifts and translates by the three rational 2-torsion points. It finds 28 finite, distinct X coordinates. Sixteen have all first-three factors square; three have square X and all five factors square, but those three repeat existing columns. No new complete column was found. All 16 finite non-torsion chord certificates include exact slopes, intercepts, factor-polynomial coefficients and derived roots.

A useful dependence was independently found and checked:

    P1 = P2 + P3,

where the P_i correspond in order to the four saved w. The four supplied lifts are therefore not four independent generators. A concrete curve-only false positive is

    X(2P1) = 388178927262389025 / 459759364.

The first three X+A_i are exact squares, but X and the last two factors are not. Modulo 37, X has residue 18, a nonsquare; X+A_5 has residue 32, also a nonsquare. This cheaply disproves a full lift of that particular point.

`inventor_local_checks.py` tests the square-residue gates at every odd prime below 200, conservatively skipping affine checks with noninvertible denominators. All original columns pass. Prime 197 rejects all 25 failed lifts in the finite discovery pool; it was selected **after** observing that pool. In `inventor_holdout.py`, prime 197 is then frozen before a second batch (triples and sums of three supplied points). After deduplicating prior X coordinates, six new finite X remain; all six fail the fixed filter and none is a column. This tiny held-out batch measures only that specific filter's usefulness here, not a general success probability.

`inventor_residue_group.py` fully enumerates the good-reduction curve over F197. The first three shifts are 83,81,63, pairwise distinct. The curve has 204 points including infinity. The known-point orders are (17,51,51,17). P2 generates the 51-point subgroup containing all supplied points, with discrete logs

    (P1,P2,P3,P4) = (42,1,41,39) mod 51.

The complete-lift residue conditions admit only nine points on the full finite curve: infinity and ± the four saved reductions. In the P2 cycle their logs are

    S = {0,1,9,10,12,39,41,42,50}.

Consequently a necessary sieve for supplied-generator combinations is

    mP2+nP3+rP4:  (m+41n+39r) mod 51 ∈ S.

This rejects 42 of 51 coefficient residue states before expensive exact rational arithmetic. That is an exact finite-state fraction, not a stochastic rejection-rate claim. It does not constrain rational points outside the subgroup generated over Q by the supplied points, and does not establish that subgroup is all of E(Q).

The PM independently checked the direct w congruences at 197: eight affine residues, exactly ± the four known w residues, plus infinity. This is the same local arithmetic information as the curve filter, not independent evidence or a generally stronger congruence. The specific operational benefit is to push this necessary condition backward to coefficient states **before** computing large rational group combinations. Direct congruence filtering remains appropriate when w itself is already available.

Successive residue gates retain 204 → 51 → 25 → 15 → 9 states: full curve, first three row squares, square X, fourth row, fifth row, respectively, always including infinity. The first-three-square set is exactly the supplied 51-point finite subgroup. This verifies on this finite curve that those first three constraints have already been absorbed by the group representation; the last three gates provide the new discrimination. It is a finite equality at this prime, not a computation of a rational descent group.

The projective denominator branch is explicit: (P:Q)=(1:0) makes every homogeneous square test P²+A_iQ² a square modulo any prime. Infinity must survive. A fixed finite collection of such tests cannot itself establish global nonextension. The finite-group script uses primitive projective coordinates to reduce rational points, checks the declared candidate reductions lie in the generated subgroup, and saves exact states. The critic independently replayed the curve cardinality, point orders/logs, nine allowed states, and 22 serialized non-torsion discovery/held-out reductions. Its negative controls reject dropping infinity or admitting residue 2. Critic also independently replayed all 16 chord certificates and corrupted-point/root controls.

A concrete boundary negative control is now saved in `inventor_infinity.py/json`: Q=2P2+P4−P3 is finite over Q but reduces to infinity. It has

    X = 38407318419797598890385717255016907776 / 168349157708154767311638516561.

The reduced X and Y denominators have 197-adic valuations 2 and 3; all three certified row-root denominators have valuation 1. Its primitive projective reduction is (0:160:0)=(0:1:0). Three exact chord steps preserve and serialize the row-root witnesses. A naive affine inverse fails on the X denominator. This is an actual quotient/partial-lift point lost by rejecting infinity, rather than merely an abstract finite-field state. It is **not** a full column: X and rows four and five remain nonsquares. An exact consecutive-square gap for the numerator of X is saved. No missed full solution follows from this negative control. The construction is one short exact combination, not a search.

## Gate, next test and limits

Recommended **GO** for a bounded coefficient-state sieve and lift-certificate study. Freeze a second good prime before generating a fresh short coefficient batch; combine its finite-state condition with the existing mod-51 condition, retain infinity, and compare candidates admitted/rejected before rational arithmetic. Every admitted candidate must still pass all exact lift gates and distinctness. A second discriminator should be useful on currently admitted coefficient classes, not merely reproduce rejection of already rejected points. Do not expand a blind denominator scan.

**HOLD** global nonextension, generator completeness/saturation, novelty, and full search certification. **NO-GO** cycle identities alone, bare quotient points, duplicated columns, or an inference from the finite batches to all rational w. The different quotient used by the domain role includes X itself among three square factors; its candidates and masks must not be conflated with this role's first-three-row quotient.

Evidence: exact rational/integer Python calculations, explicit finite witnesses and independent replay; no inventor Lean theorem or physical result. The mathematically standard good-reduction bridge is stated as an additional theorem dependency rather than silently counted as kernel-checked here. Scripts passed local Ruff formatting and lint. Repository-wide integrated checks belong to the PM and are not implied by these local checks.

Quality rubric: faithfulness 4/4, reproducibility 4/4, discriminatory value 4/4, critique 4/4, actionability 3/4 = 19/20 (95%). Subjective confidence is high in the finite computations; confidence that this route will produce a fifth column is uncalibrated and substantially lower. No new column or solution of Erdős 885 is claimed.
