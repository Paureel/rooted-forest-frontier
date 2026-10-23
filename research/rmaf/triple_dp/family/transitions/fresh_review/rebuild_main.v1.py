#!/usr/bin/env python3
"""One-shot fresh isolated Lean review driver, independent of author build code.
Archives copied source, commands, diagnostics, timings, axiom queries and hashes.
A failing import is never accepted as a mathematical negative-control catch.
"""
import argparse
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import time

ROOT = pathlib.Path(__file__).resolve().parents[6]
HERE = pathlib.Path(__file__).resolve().parent
SOURCE = HERE.parent
RESULT = ROOT / 'research/rmaf/results'
SNAP = HERE / 'main_snapshot'
MODULES = [
    ('TripleDP', ROOT / 'research/rmaf/triple_dp/TripleDP.lean'),
    ('ConnectedRegions', ROOT / 'research/rmaf/triple_dp/ConnectedRegions.lean'),
    ('FamilyAssembly', ROOT / 'research/rmaf/triple_dp/family/cost_route/FamilyAssembly.lean'),
    *[(name, SOURCE / (name + '.lean')) for name in ['FiniteSelection', 'FamilyMerge', 'MergeContract', 'MergeControls']]
]
NEGATIVES = [('FalseMergeCost', 'T1.cost', 1, 0), ('FalseMergeCount', 'T1.blockCount', 2, 1), ('FalseCoalesce', 'T3.blockCount', 1, 3), ('FalseDoubleCharge', 'T4.cost', 6, 3)]
ENV = dict(os.environ, ELAN_HOME=str(ROOT / '.runtime/elan'), LEAN_PATH=str(SNAP))

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify_pin():
    pin = json.loads((SOURCE / 'MAIN-MERGE-SHA256.json').read_text())
    return [{'path': name, 'sha256': digest(SOURCE / name), 'expected': sha, 'match': digest(SOURCE / name) == sha} for name, sha in pin['files'].items()]

def run(name, output=True):
    command = [str(ROOT / 'bootloops-lean')]
    if output: command += ['-o', str(SNAP / (name + '.olean'))]
    command += [str(SNAP / (name + '.lean'))]
    start = time.perf_counter()
    result = subprocess.run(command, cwd=SNAP, env=ENV, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=90)
    log = RESULT / ('triple-family-transitions-fresh-' + name + '.log')
    log.write_text(result.stdout)
    query_names = re.findall(r'^#print axioms (\S+)', (SNAP / (name + '.lean')).read_text(), flags=re.M)
    axioms = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", result.stdout, flags=re.S)
    names = sorted({a.strip() for _, group in axioms for a in group.split(',') if a.strip()})
    record = {'module': name, 'command': command, 'cwd': str(SNAP), 'elapsed_seconds': time.perf_counter() - start, 'exit_code': result.returncode, 'source_sha256': digest(SNAP / (name + '.lean')), 'source_queries': query_names, 'actual_query_count': len(axioms), 'actual_axioms': names, 'log': str(log)}
    print(json.dumps({key: record[key] for key in ['module', 'elapsed_seconds', 'exit_code', 'actual_query_count', 'actual_axioms']}), flush=True)
    return record, result.stdout

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pilot', action='store_true')
    args = parser.parse_args()
    pin_rows = verify_pin()
    assert all(row['match'] for row in pin_rows), pin_rows
    if args.pilot:
        SNAP.mkdir(exist_ok=False)
        for name, path in MODULES:
            shutil.copyfile(path, SNAP / (name + '.lean'))
        for name, expr, wrong, clean in NEGATIVES:
            shutil.copyfile(SOURCE / (name + '.lean'), SNAP / (name + '.lean'))
            text = (SNAP / (name + '.lean')).read_text()
            assert text.count(expr + ' = ' + str(wrong)) == 1
            (SNAP / (name + 'Clean.lean')).write_text(text.replace(expr + ' = ' + str(wrong), expr + ' = ' + str(clean)))
        (SNAP / 'MalformedFresh.lean').write_text('import MissingFreshMergeReviewImport\nexample : (0 : Nat) = 1 := by decide\n')
        source_scan = {}
        for path in SNAP.glob('*.lean'):
            body = path.read_text()
            source_scan[path.name] = re.findall(r'\b(?:sorry|sorryAx|admit|native_decide|axiom|unsafe|implemented_by)\b', body)
        assert all(not bad for bad in source_scan.values()), source_scan
        (HERE / 'main-source-manifest.json').write_text(json.dumps({'pinned_files': pin_rows, 'source_scan': source_scan, 'sources': {name: {'original': str(path), 'sha256': digest(path)} for name, path in MODULES}, 'environment': {'ELAN_HOME': ENV['ELAN_HOME'], 'LEAN_PATH': ENV['LEAN_PATH']}}, indent=2) + '\n')
        chosen = MODULES[:1]
    else:
        chosen = MODULES[1:]
    records = []
    for name, original in chosen:
        assert digest(original) == digest(SNAP / (name + '.lean'))
        record, log = run(name)
        records.append(record)
        assert record['exit_code'] == 0, record
        assert record['actual_query_count'] == len(record['source_queries']), record
        assert set(record['actual_axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}, record
        assert not re.search(r'\bsorry|native_decide|sorryAx', log), record
    if not args.pilot:
        for name, expr, wrong, clean in NEGATIVES:
            record, log = run(name, False)
            records.append(record)
            assert record['exit_code'] != 0
            assert 'evaluated to false' in log and expr + ' = ' + str(wrong) in log, log
            assert not re.search(r'unknown module|object file|failed to load|unknown constant|unexpected token', log, flags=re.I), log
            record['negative_classification'] = 'exact mathematical false proposition'
            twin, _ = run(name + 'Clean', False)
            records.append(twin)
            assert twin['exit_code'] == 0
        record, log = run('MalformedFresh', False)
        records.append(record)
        assert record['exit_code'] != 0 and 'MissingFreshMergeReviewImport' in log
        assert 'evaluated to false' not in log
        record['negative_classification'] = 'import error rejected as mathematical evidence'
    assert all(row['match'] for row in verify_pin())
    receipt = {'pilot': args.pilot, 'records': records, 'pin_unchanged': verify_pin()}
    (RESULT / ('triple-family-transitions-fresh-lean-' + ('pilot' if args.pilot else 'main') + '.json')).write_text(json.dumps(receipt, indent=2) + '\n')

if __name__ == '__main__': main()
