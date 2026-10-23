"""Author audit of the completed one-tree interface; not an independent oracle.
Run from workspace root with ./bootloops-python. Outputs remain in degree_two/audit.
"""
from pathlib import Path
import re, json, hashlib, subprocess, os, time
ROOT = Path('research/rmaf/bridge_review/degree_two')
MODULES = [('LocalSplit','DegreeTwo'), ('DegreeCounting','DegreeTwo'),
           ('LocalSplitControls','DegreeTwo.LocalControls'), ('AgreementBlock','DegreeTwo')]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    items, rows = [], []
    env = os.environ.copy()
    env['LEAN_PATH'] = str(ROOT/'audit/deps')
    for module, namespace in MODULES:
        source = ROOT/'lean'/f'{module}.lean'
        pin = digest(source)
        for kind, name in re.findall(r'^(theorem|def)\s+(\w+)', source.read_text(), re.M):
            items.append(dict(kind=kind, name=namespace+'.'+name, module=module,
                              source=str(source), sha256=pin))
        log = ROOT/'audit'/f'{module}-checkpoint.log'
        started = time.monotonic()
        run = subprocess.run(['./bootloops-lean','-o',str(ROOT/'audit/deps'/f'{module}.olean'),str(source)],
                             env=env, capture_output=True, text=True)
        log.write_text(run.stdout+run.stderr)
        rows.append(dict(module=module, exit_code=run.returncode,
                         seconds=time.monotonic()-started, log=str(log),
                         source_sha256=pin, log_sha256=digest(log)))
        assert run.returncode == 0, (module, run.stdout, run.stderr)
        assert digest(source) == pin, 'Source changed while compiling'
    source = ROOT/'audit/OneTreeAxioms.lean'
    source.write_text('\n'.join('import '+module for module,_ in MODULES)+'\n\n'+
                      '\n'.join('#print axioms '+item['name'] for item in items)+'\n')
    run = subprocess.run(['./bootloops-lean',str(source)],env=env,capture_output=True,text=True)
    log = ROOT/'audit/one-tree-axioms.log'
    log.write_text(run.stdout+run.stderr)
    assert run.returncode == 0, run.stdout+run.stderr
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log.read_text())
    assert len(reports) == len(items), (len(reports),len(items))
    allowed = {'propext','Classical.choice','Quot.sound'}
    for name, axioms in reports:
        assert {x.strip() for x in axioms.split(',') if x.strip()} <= allowed, (name,axioms)
    receipt = dict(status='author-kernel-check-only-fresh-review-pending',
        scope='One-tree split, exact finite degree interpretation, block premises from original agreement; no cross-tree disjointness theorem yet.',
        source_declarations=items, builds=rows, axiom_report_count=len(reports),
        axioms_allowed=sorted(allowed), axiom_log=str(log), axiom_log_sha256=digest(log),
        script=str(Path(__file__).relative_to(Path.cwd())), script_sha256=digest(Path(__file__)),
        lineage='Author-run kernel audit; declaration parsing reused prior checkpoint pattern, not independent mathematical confirmation.')
    (ROOT/'audit/one-tree-checkpoint-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(dict(builds_passed=len(rows),declarations_audited=len(reports),all_axioms_standard=True)))

if __name__ == '__main__':
    main()
