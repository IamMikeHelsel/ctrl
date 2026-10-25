"""
Pure standard-library tests verifying the mathematical identities of 6x6 real
skew-symmetric matrices, block normal form, and the Same-Square comparator.
No third-party packages (no numpy) required.
"""

from fractions import Fraction


def mat_mul(A, B):
    n = len(A)
    m = len(B[0])
    p = len(B)
    return [[sum(A[i][k] * B[k][j] for k in range(p)) for j in range(m)] for i in range(n)]


def mat_transpose(A):
    n = len(A)
    m = len(A[0])
    return [[A[j][i] for j in range(n)] for i in range(m)]


def mat_add(A, B):
    return [[A[i][j] + B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_sub(A, B):
    return [[A[i][j] - B[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_neg(A):
    return [[-A[i][j] for j in range(len(A[0]))] for i in range(len(A))]


def mat_frobenius_sq(A):
    return sum(A[i][j] ** 2 for i in range(len(A)) for j in range(len(A[0])))


def make_skew_witness(a, b):
    M = [[Fraction(0)] * 6 for _ in range(6)]
    M[0][1] = Fraction(a)
    M[1][0] = -Fraction(a)
    M[2][3] = Fraction(b)
    M[3][2] = -Fraction(b)
    return M


def make_symmetric_witness(a, b):
    M = [[Fraction(0)] * 6 for _ in range(6)]
    M[0][1] = Fraction(a)
    M[1][0] = Fraction(a)
    M[2][3] = Fraction(b)
    M[3][2] = Fraction(b)
    return M


def test_same_square_algebraic_identity():
    """Verify S^2 == -K^2 exactly in rational arithmetic."""
    for a, b in [(1, 2), (3, 4), (0, 5), (7, 0), (0, 0)]:
        K = make_skew_witness(a, b)
        S = make_symmetric_witness(a, b)

        # Check S is symmetric
        assert mat_transpose(S) == S
        # Check K is skew-symmetric
        assert mat_transpose(K) == mat_neg(K)

        # Check S^2 == -K^2
        S2 = mat_mul(S, S)
        K2 = mat_mul(K, K)
        neg_K2 = mat_neg(K2)
        assert S2 == neg_K2

        # Check Frobenius norm squared is identical
        assert mat_frobenius_sq(S) == mat_frobenius_sq(K)
        assert mat_frobenius_sq(K) == 2 * (Fraction(a)**2 + Fraction(b)**2)


def test_commutator_with_diagonal_squares():
    """Verify that any skew matrix K commuting with its own square -K^2 = diag(d)
    satisfies K_ij * (d_j - d_i) == 0."""
    # Let K be a block diagonal skew matrix:
    a = Fraction(3, 2)
    b = Fraction(4, 5)
    K = make_skew_witness(a, b)
    neg_K2 = mat_neg(mat_mul(K, K))

    # Diagonal entries of -K^2: [a^2, a^2, b^2, b^2, 0, 0]
    d = [neg_K2[i][i] for i in range(6)]
    for i in range(6):
        for j in range(6):
            if i != j:
                assert neg_K2[i][j] == 0  # pure diagonal

    # Check (d_j - d_i) * K_ij == 0 for all i, j
    for i in range(6):
        for j in range(6):
            diff = d[j] - d[i]
            assert diff * K[i][j] == 0


def test_lyapunov_comparator_prepared_coordinates():
    """Verify Formula (1) and gain difference in prepared coordinates."""
    a = Fraction(2)
    b = Fraction(3)
    K = make_skew_witness(a, b)
    S = make_symmetric_witness(a, b)

    # In prepared coordinates, A has A_03 = 0, A_12 = 0
    # Create arbitrary rational matrix A
    A = [[Fraction(i * 3 + j - 5, 4) for j in range(6)] for i in range(6)]
    A[0][3] = Fraction(0)
    A[1][2] = Fraction(0)

    # L_A(X) = A X + X A^T
    AT = mat_transpose(A)
    LA_K = mat_add(mat_mul(A, K), mat_mul(K, AT))
    LA_S = mat_add(mat_mul(A, S), mat_mul(S, AT))

    frob_K = mat_frobenius_sq(LA_K)
    frob_S = mat_frobenius_sq(LA_S)

    # Gain difference formula: 4*a^2*(A_01^2 + A_10^2) + 4*b^2*(A_23^2 + A_32^2)
    expected_gain = (
        4 * (a ** 2) * (A[0][1] ** 2 + A[1][0] ** 2) +
        4 * (b ** 2) * (A[2][3] ** 2 + A[3][2] ** 2)
    )
    assert frob_S - frob_K == expected_gain
    assert frob_S >= frob_K
