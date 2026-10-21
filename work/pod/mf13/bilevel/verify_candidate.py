"""verify_candidate.py  FILE.json  [dps]

Loads A (list of lists of decimal strings, 40 digits) from a candidate JSON, rebuilds the n^2 x n^2 operator
I(x)A + A(x)I of L_A(X)=AX+XA^T (column-wise vec), restricts it to the symmetric / skew subspaces using exact
orthonormal bases (mpmath, default 50 digits), computes both spectral norms by mpmath SVD, and prints
   ||L_A|S||, ||L_A|K||, and the gap  ||L_A|K|| - ||L_A|S||.
A strict counterexample to the Byers-Nash symmetric-maximizer conjecture needs  ||L_A|K|| > ||L_A|S||.
Independent of all search code (uses only mpmath).
"""
import sys, json
import mpmath as mp


def load_A(fn):
    d = json.load(open(fn))
    A = d['A'] if 'A' in d else d
    return mp.matrix([[mp.mpf(x) for x in row] for row in A])


def restricted_norms(A):
    n = A.rows
    N = n * n
    I = mp.eye(n)
    # operator in vec (row-major, vec(X)[i*n+j] = X[i,j]):  vec(AX + XA^T)  -> (A (x) I + I (x) A)
    M = mp.zeros(N, N)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                # (AX)[i,j] = sum_k A[i,k] X[k,j] ; (XA^T)[i,j] = sum_k X[i,k] A[j,k]
                M[i * n + j, k * n + j] += A[i, k]
                M[i * n + j, i * n + k] += A[j, k]
    r2 = mp.sqrt(2)
    Sb, Kb = [], []
    for i in range(n):
        v = mp.zeros(N, 1); v[i * n + i] = 1; Sb.append(v)
    for i in range(n):
        for j in range(i + 1, n):
            v = mp.zeros(N, 1); v[i * n + j] = 1 / r2; v[j * n + i] = 1 / r2; Sb.append(v)
            w = mp.zeros(N, 1); w[i * n + j] = 1 / r2; w[j * n + i] = -1 / r2; Kb.append(w)
    out = []
    for B in (Sb, Kb):
        m = len(B)
        U = mp.zeros(N, m)
        for c, v in enumerate(B):
            for r in range(N):
                U[r, c] = v[r]
        R = U.T * M * U
        sv = mp.svd_r(R, compute_uv=False)
        out.append(max(sv))
    return out[0], out[1]


if __name__ == '__main__':
    fn = sys.argv[1]
    mp.mp.dps = int(sys.argv[2]) if len(sys.argv) > 2 else 50
    A = load_A(fn)
    s, k = restricted_norms(A)
    print("n =", A.rows)
    print("||L_A|_S|| =", mp.nstr(s, 30))
    print("||L_A|_K|| =", mp.nstr(k, 30))
    print("gap  ||K|| - ||S|| =", mp.nstr(k - s, 20))
    print("ratio S/K =", mp.nstr(s / k, 30))
    print("COUNTEREXAMPLE (skew norm > sym norm):", bool(k > s))
