"""Isolated audit for the labelled-family normal-form continuation.

This problem-specific wrapper rebuilds preserved dependencies and records
new proof declarations separately from the earlier triple-DP receipts.
"""
import argparse
import hashlib
import json
import os
import pathlib
import re
import subprocess
import time

HERE = pathlib.Path(__file__).resolve().parent
RMAF = HERE.parents[1]
ROOT = RMAF.parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--receipt', default='triple-family-lean-v1.json')
    parser.add_argument('--geometry', action='store_true')
    args = parser.parse_args()
    output = RMAF/'results'/args.receipt
    assert output.parent == RMAF/'results' and output.name.startswith('triple-family-')
    assert not output.exists(), 'preserve earlier receipt; give a new --receipt name'
    deps = HERE/'.audit-deps'
    deps.mkdir(exist_ok=True)
    env = dict(os.environ, ELAN_HOME=str(ROOT/'.runtime/elan'), LEAN_PATH=str(deps))
    entries = [(HERE.parent/'TripleDP.lean', True),
               (HERE.parent/'ConnectedRegions.lean', True),
               (HERE/'FamilyModel.lean', False), (HERE/'FamilyTrim.lean', False),
               (HERE/'FamilyControls.lean', False), (HERE/'NegativeFamily.lean', False)]
    if args.geometry:
        entries[2:2] = [(HERE/'path_route/PathStem.lean', True)]
        entries[-1:-1] = [(HERE/'FamilyGeometry.lean', False)]
    rows = []
    for src, dependency in entries:
        negative = src.name == 'NegativeFamily.lean'
        command = [str(ROOT/'bootloops-lean')]
        if not negative:
            command += ['-o', str(deps/src.with_suffix('.olean').name)]
        command += [str(src)]
        start = time.perf_counter()
        process = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True)
        log = process.stdout + process.stderr
        log_path = HERE/(output.stem+'-'+src.stem+'.log')
        log_path.write_text(log)
        audits = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
        if negative:
            assert process.returncode != 0 and 'decide' in log and 'is false' in log, log
            assert '0 = 1' in log, log
        else:
            assert process.returncode == 0 and 'sorryAx' not in log, log
            assert re.search(r'\b(sorry|admit|native_decide)\b',src.read_text()) is None
            assert re.search(r'^\s*axiom\b',src.read_text(),re.MULTILINE) is None
            for _, names in audits:
                assert set(filter(None,(x.strip() for x in names.split(',')))) <= {'propext','Classical.choice','Quot.sound'}
        rows.append(dict(file=str(src.relative_to(ROOT)), dependency=dependency,
                         negative=negative, returncode=process.returncode,
                         seconds=time.perf_counter()-start, command=command,
                         checked_axioms=audits, sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
                         log=str(log_path.relative_to(ROOT))))
    version = subprocess.run([str(ROOT/'bootloops-lean'),'--version'],env=env,cwd=ROOT,capture_output=True,text=True)
    assert version.returncode == 0 and '4.35.0' in version.stdout
    new = sum(len(r['checked_axioms']) for r in rows if not r['dependency'] and not r['negative'])
    assert new == (39 if args.geometry else 31), new
    result = dict(status='passed', version=version.stdout.strip(), builds=rows,
                  new_audited_declarations=new, new_audited_theorems=new-1,
                  new_audited_constructor='TripleDP.Family.normalize',
                  dependency_audits=43 if args.geometry else 27, negative_control='caught',
                  auditor_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                  scope='Universal finite-address labelled-family normalization with empty-open pruning; four-transition correspondence and executable graph bridge remain OPEN.')
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','new_audited_declarations','new_audited_theorems','negative_control']}))


if __name__ == '__main__':
    main()
