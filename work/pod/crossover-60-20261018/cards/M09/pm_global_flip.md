# Conditional smooth global sign flip — hand derivation

AI-written. This is not a Lean bundle theorem or a completed source-to-bundle binding.
Assume a finite-rank smooth complex vector bundle over a paracompact smooth base,
a smooth nondegenerate Hermitian form K, and a globally defined smooth complex-linear
W with W²=-I and K(Wu,v)=K(u,Wv). Use conjugate-linear first-slot convention.

The projectors (I−iW)/2 and (I+iW)/2 define smooth eigenbundles E+ and E−
(eigenvalues+i and−i). Their ranks are locally constant. Each is K-null:
for u,v in E+, selfadjointness gives−iK(u,v)=iK(u,v), hence K(u,v)=0;
likewise E−. Nondegeneracy of K then makes its cross-pairing nondegenerate,
so the two finite ranks coincide and K identifies E− with the anti-dual of E+.

Choose any smooth positive Hermitian metric h on E+; this is an explicit
auxiliary choice, available under the paracompact smooth-bundle assumption.
Define the unique smooth complex-linear isomorphism F:E+→E− by
K(u,Fv)=h(u,v). Define G(u+Fv)=v+Fu. Then G²=I and GW=−WG.
For x=u+Fv,y=u′+Fv′,
K(x,y)=h(u,v′)+h(v,u′), using Hermitian symmetry for the second summand.
Swapping u and v preserves this sum, so G†KG=K.
Consequently G†H_tG=H_−t globally for constant real t (also pointwise for real t(x)).

This avoids the unnecessary requirement of a globally chosen negative Clifford
vector. Local gamma7 is one explicit fiber witness; this global construction
is a different, generally noncanonical bundle map. It need not commute with the
Spin representation or preserve fixed W/gamma. It only closes the sign flip for
the full smooth fixed-K unitary gauge group under the declared bundle hypotheses.
The source must still supply a global W and the field/adjoint interpretation;
H_t is not established as an independently allowed source field. Nonconstant
G requires its derivative in the connection action. The arbitrary auxiliary
h is not an extra physical observable unless explicitly made one.

Domain independently checked the cross-pairing and complex-linearity argument.
Critic independently reviewed the complete hand construction; see critic.md. No novelty or physical-modulus claim.
