"""Bounded exact probe, not a proof of Shallit's infinite Hankel conjecture."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import time

N, MAX_ORDER = 4096, 128
MORPHISM = {1: (1, 2), 2: (2, 3), 3: (1, 4), 4: (3, 2)}


def bareiss(matrix):
    a = [row[:] for row in matrix]
    sign, previous = 1, 1
    for k in range(len(a) - 1):
        if not a[k][k]:
            j = next((j for j in range(k + 1, len(a)) if a[j][k]), None)
            if j is None:
                return 0
            a[k], a[j] = a[j], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, len(a)):
            for j in range(k + 1, len(a)):
                v = a[i][j] * pivot - a[i][k] * a[k][j]
                assert v % previous == 0
                a[i][j] = v // previous
        for i in range(k + 1, len(a)):
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def main():
    started = time.perf_counter()
    seq = [1]
    while len(seq) < N:
        seq = [y for x in seq for y in MORPHISM[x]]
    seq = seq[:N]
    assert seq[:16] == list(map(int, '1223231423141232'))
    # H(n,k)=det(seq[k+i+j]) for i,j in 0..n-1. Desnanot-Jacobi:
    # H(n,k)H(n-2,k+2)=H(n-1,k)H(n-1,k+2)-H(n-1,k+1)^2.
    previous2, previous = [1] * (N + 2), seq
    count = N
    checked = []
    first_zero = None
    max_bits = max(seq).bit_length()
    completed_order = 1
    for n in range(2, MAX_ORDER + 1):
        row = []
        for k in range(N - 2*n + 2):
            numerator = previous[k] * previous[k+2] - previous[k+1]**2
            denominator = previous2[k+2]
            assert denominator != 0
            assert numerator % denominator == 0
            value = numerator // denominator
            count += 1
            max_bits = max(max_bits, abs(value).bit_length())
            if value == 0:
                first_zero = {'order': n, 'shift': k, 'window': seq[k:k+2*n-1]}
                break
            row.append(value)
        if first_zero:
            break
        if n <= 16 or n in [24, 32]:
            for k in sorted({0, len(row)//3, len(row)-1}):
                independent = bareiss([[seq[k+i+j] for j in range(n)] for i in range(n)])
                assert independent == row[k]
                checked.append({'order':n, 'shift':k, 'determinant':str(independent)})
        previous2, previous = previous, row
        completed_order = n
    result = {
        'status': 'counterexample_candidate' if first_zero else 'bounded_search_no_zero',
        'recorded_utc': datetime.now(timezone.utc).isoformat(),
        'source_url': 'https://cs.uwaterloo.ca/~shallit/Talks/bc4.pdf',
        'source_slide': 35, 'prefix_length': N, 'max_order_requested': MAX_ORDER,
        'max_order_completed': completed_order,
        'tested_condition': '1 <= n <= 128; 0 <= k <= 4096 - 2*n + 1',
        'integer_determinants_checked': count, 'max_determinant_bits': max_bits,
        'first_zero': first_zero,
        'independent_bareiss_samples': checked,
        'elapsed_seconds': time.perf_counter()-started,
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'sequence_sha256': hashlib.sha256(bytes(seq)).hexdigest(),
        'proof_boundary': 'Exact integer experiment, not Lean-checked; does not settle infinite sequence or establish novelty/prize eligibility.'
    }
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'independent_bareiss_samples'}, indent=2))
    print('independent Bareiss checks:', len(checked))


if __name__ == '__main__':
    main()
