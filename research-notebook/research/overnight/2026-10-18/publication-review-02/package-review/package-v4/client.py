#!/usr/bin/env python3
"""Check one exact-rational commit request against a completed fresh replay.

This is an offline proof client. It does not read clocks or control a robot.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess
import replay
from rational_input import keys, pending, base, task, timing

HERE = Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok, message):
    if not ok: raise RuntimeError(message)
def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result: raise ValueError('Duplicate JSON key: ' + key)
        result[key] = value
    return result

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input', type=Path, required=True)
    ap.add_argument('--replay-output', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    frozen, binding = replay.verify_inputs()
    verified = args.replay_output.resolve()
    metadata = json.loads((verified / 'results.json').read_text())
    require(metadata['passed'] is True, 'Replay did not pass')
    require(metadata['input_manifest_sha256'] == sha(HERE / 'input-manifest.json'), 'Different replay inputs')
    require(metadata['local_source_sha256'] == {m:i['sha256'] for m,i in binding['modules'].items()}, 'Replay source set')
    require(set(metadata['compiled_module_names']) == set(binding['modules']), 'Compiled module coverage')
    fresh = verified / '.build'
    actual_objects = {str(p.relative_to(fresh)): sha(p) for p in sorted(fresh.rglob('*'))
                      if p.is_file() and '.olean' in p.name}
    require(actual_objects == metadata['compiled_objects'], 'Changed replay objects')
    require(all(m.replace('.', '/') + '.olean' in actual_objects for m in binding['modules']), 'Missing local object')
    for module, item in binding['modules'].items():
        require(sha(fresh / (module.replace('.', '/') + '.lean')) == item['sha256'], 'Changed replay source: ' + module)
    compiler = Path(metadata['lean_executable']); checker = Path(metadata['checker_executable'])
    require(sha(compiler) == metadata['lean_sha256'] and sha(checker) == metadata['checker_sha256'], 'Changed tool binary')
    search = metadata['lean_path'].split(os.pathsep)
    require(Path(search[0]).resolve() == fresh, 'Replay search path')
    raw = args.input.read_bytes()
    require(len(raw) <= 1_000_000, 'Input exceeds prototype file limit')
    value = json.loads(raw, object_pairs_hook=unique_pairs)
    keys(value, ['pending', 'liveBase', 'liveTask', 'timing'])
    source = ('import FutureCommit\nnamespace ExactClient\n'
              'open RobotMotion RobotMotion.FutureCommit\n'
              'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n')
    source += 'def p : Pending := ' + pending(value['pending']) + '\n'
    source += 'def b : Base := ' + base(value['liveBase']) + '\n'
    source += 'def t : Task := ' + task(value['liveTask']) + '\n'
    source += 'def tm : Timing := ' + timing(value['timing']) + '\n'
    out = args.output.resolve()
    require(not out.exists(), 'Output must be new')
    require(out != HERE and HERE not in out.parents, 'Keep client outputs outside the proof package')
    require(out != verified and verified not in out.parents, 'Keep client outputs outside the completed replay')
    out.mkdir(parents=True)
    (out / 'input.json').write_bytes(raw)
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(out)] + search)
    env['PATH'] = str(compiler.parent) + os.pathsep + env.get('PATH', '')
    def run(argv, name):
        proc = subprocess.run([str(a) for a in argv], cwd=out, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
        (out / (name + '.log')).write_text(proc.stdout)
        require(proc.returncode == 0, name + ' failed; evidence retained')
        return proc.stdout
    probe = out / 'ClientProbe.lean'
    probe.write_text(source + '#eval commitOK p b t tm\nend ExactClient\n')
    observed = run([compiler, '--root=' + str(out), probe], 'probe').strip()
    require(observed in {'true', 'false'}, 'Unexpected evaluator output')
    proof = 'theorem decision : commitOK p b t tm = ' + observed + ' := by decide +kernel\n'
    if observed == 'true':
        proof += ('theorem reference_contract : ReferenceContract b t (commit p b t tm) p.execution := '
                  '(successful_commit_contract decision).2.2.2.2.2\n')
        conclusion = 'reference_contract'
    else:
        proof += 'theorem retained_live : commit p b t tm = b := rejected_retains_live decision\n'
        conclusion = 'retained_live'
    path = out / 'ClientProof.lean'
    path.write_text(source + proof + '#print axioms decision\n#print axioms ' + conclusion + '\nend ExactClient\n')
    log = run([compiler, '--root=' + str(out), '-o', path.with_suffix('.olean'), path], 'proof')
    for name in ['decision', conclusion]:
        entries = re.findall(r"'ExactClient\." + name + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
        require(len(entries) == 1, 'Missing generated-theorem axiom audit: ' + name)
        listing = entries[0]
        require(set(x.strip() for x in listing.split(',') if x.strip()) <=
                {'propext', 'Classical.choice', 'Quot.sound'}, 'Unexpected client axiom')
    run([checker, 'ClientProof', '-v'], 'kernel')
    require(replay.verify_inputs()[0] == frozen, 'Package changed during client run')
    require(actual_objects == {str(p.relative_to(fresh)): sha(p) for p in sorted(fresh.rglob('*'))
                              if p.is_file() and '.olean' in p.name}, 'Replay objects changed during client run')
    require((out / 'input.json').read_bytes() == raw, 'Input snapshot changed during proof')
    result = {'decision': observed == 'true', 'compiled_proof': True, 'kernel_replay': True,
              'input_sha256': hashlib.sha256(raw).hexdigest(), 'proof_source_sha256': sha(path),
              'proof_object_sha256': sha(path.with_suffix('.olean')),
              'meaning': 'Reference contract for the supplied live state and ideal timing inputs.'
                if observed == 'true' else 'Live state retained. The new task is not certified.',
              'boundary': 'Offline client. Parsing, measured clocks, atomic execution and physical premises are not formally verified.'}
    (out / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__': main()
