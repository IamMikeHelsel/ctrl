# Independent two-parameter determinant audit

Keep all eight output coefficients fixed to the shared A3–A5 values, and write a=c1L3,b=c2L3. The independently checked identity for the reconstructed, doubled scalar-pairing matrix is

`det M(a,b) = 2^491·3^43·5^21·7^8 · (5a+6b)^21 · (5a−3b)^35`.

`domain_two_parameter.py` reconstructs the union support graph from the two saved endpoint matrices, finds64 disjoint7×7 blocks, and computes every block coefficient by memoized Laplace expansion. It imports neither the PM symbol assembly nor its graph/elimination algorithms. There are8 constant blocks,21 blocks proportional to5a+6b, and35 proportional to5a−3b. The product of normalizing constants and both regrouping permutation signs is the positive constant displayed above.

The source injection is linear in(a,b) on precisely the56 L3 rows; all other rows are fixed. Each nonconstant block has precisely one such row. Determinant multilinearity therefore promotes the two endpoint computations to an identity for arbitrary rational or real(a,b), conditional on that source-bound symbolic row structure. This is not interpolation from a few determinant values.

Two representative source blocks have additionally been constructed directly from the elementary exterior API, avoiding the PM full symbol code. `domain_sign_block.py` gives768(5a−3b); the current script independently reconstructs the other class from inputw123 plus the first Y2/Y4+ chains and obtains640(5a+6b). The latter is checked at(1,0),(0,1),(2,−1),(6,−5), including its singular line.

Full-matrix inputs are shared artifacts; the critic's separate bitmask reconstruction supplies independent entry verification. The arithmetic algorithm and both literal representative blocks here provide another independent route through the sign issue. No Lean/kernel proof is claimed.

Consequences: at A3=(1,1) and A4=(1,0), the determinant is positive; at A5=(0,1), it is negative. Thus the fixed matrix construction has the observed mixed signs intrinsically. The printed A3/A4 negative signs remain unresolved source-binding discrepancies. This audit does not silently alter them, choose coefficient-dependent basis orientations, or declare the source erroneous.

Command:

```
uv run --no-project --python /usr/local/bin/python3 python work/pod/crossover-60-20261018/cards/M07/domain_two_parameter.py
```

Scoped Ruff check and format passed. This is a final initial-review supplement, not an extended investigation.
