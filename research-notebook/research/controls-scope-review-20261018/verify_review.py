"""Read-only replay of review bindings and arithmetic, not proof acceptance."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    inputs = json.loads((HERE/'input-bindings.json').read_text())
    for name, digest in inputs.items():
        assert sha(ROOT/name) == digest, f'review input changed: {name}'
    packet = ROOT/'publication/controls-team-review-20261018'
    frozen = json.loads((packet/'artifact-sha256.json').read_text())['files']
    for name, entry in frozen.items():
        assert sha(packet/name) == entry['sha256'], f'frozen packet changed: {name}'
    packet_inputs = json.loads((packet/'input-bindings.json').read_text())
    for name, digest in packet_inputs.items():
        assert sha(ROOT/name) == digest, f'prior bound input changed: {name}'
    with tempfile.TemporaryDirectory(prefix='controls-scope-review-') as temporary:
        script = Path(temporary)/'age_budget.py'
        script.write_bytes((HERE/'age_budget.py').read_bytes())
        run = subprocess.run([sys.executable, str(script)], capture_output=True, text=True)
        assert run.returncode == 0, run.stderr
        assert (Path(temporary)/'age-budget-results.json').read_bytes() == (HERE/'age-budget-results.json').read_bytes()
    result = {'passed': True, 'mode': 'hash preservation and exact rational arithmetic only',
              'review_inputs':len(inputs), 'prior_frozen_packet_files':len(frozen),
              'prior_packet_input_files':len(packet_inputs), 'arithmetic_replay_equal':True,
              'lean_replay_performed':False, 'independent_review_performed':False,
              'publication_novelty_established':False}
    rendered = json.dumps(result, indent=2)+'\n'
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end='')

if __name__ == '__main__':
    main()
