#!/usr/bin/env python3
"""One-shot reviewer-owned isolated Lean replay; no author runner/checker imports.
Preserves exact sources, real diagnostics, per-module query names, commands,
axioms and timings. Mathematical negatives require exact false propositions.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
RESULTS = ROOT / 'research/rmaf/results'
ORIGINAL = HERE.parents[1] / 'index_route'
AUTHOR = RESULTS / 'triple-family-transitions-index-20261014T142855430197Z'
SNAP = HERE / 'snapshot'
ENV = dict(os.environ, ELAN_HOME=str(ROOT / '.runtime/elan'), LEAN_PATH=str(SNAP))
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()


def execute(name, compile_output=True):
    command = [str(ROOT / 'bootloops-lean')]
    if compile_output: command += ['-o', str(SNAP / (name + '.olean'))]
    command.append(str(SNAP / (name + '.lean')))
    start = time.perf_counter()
    result = subprocess.run(command, cwd=SNAP, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=90)
    elapsed = time.perf_counter() - start
    log = RESULTS / ('triple-family-transitions-fresh-index-' + name + '.log')
    log.write_text(result.stdout)
    source_queries = re.findall(r'^#print axioms (\S+)', (SNAP / (name + '.lean')).read_text(), flags=re.M)
    outputs = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", result.stdout, flags=re.S)
    axioms = sorted({a.strip() for _, values in outputs for a in values.split(',') if a.strip()})
    row = {'module': name, 'command': command, 'cwd': str(SNAP), 'environment': {'ELAN_HOME': ENV['ELAN_HOME'], 'LEAN_PATH': ENV['LEAN_PATH']}, 'elapsed_seconds': elapsed, 'returncode': result.returncode, 'sha256': sha(SNAP / (name + '.lean')), 'source_query_names': source_queries, 'actual_query_names': [name for name, _ in outputs], 'actual_query_count': len(outputs), 'axioms': axioms, 'log': str(log)}
    with (RESULTS / 'triple-family-transitions-fresh-index-lean-events.jsonl').open('a') as out:
        out.write(json.dumps(row) + '\n')
    print(json.dumps({key:row[key] for key in ['module','elapsed_seconds','returncode','actual_query_count','axioms']}), flush=True)
    return row, result.stdout


def positive(name):
    row, log = execute(name)
    assert row['returncode'] == 0, log
    assert [name.rsplit('.', 1)[-1] for name in row['actual_query_names']] == row['source_query_names'], row
    assert set(row['axioms']) <= {'propext','Quot.sound','Classical.choice'}, row
    assert 'sorryAx' not in log
    return row


def main():
    prior_manifest = json.loads((HERE.parent / 'FINAL-SHA256.json').read_text())
    assert all(sha(ROOT / name) == digest for name, digest in prior_manifest['files'].items())
    pin = json.loads((ORIGINAL.parent / 'MAIN-MERGE-SHA256.json').read_text())
    assert all(sha(ORIGINAL.parent / name) == digest for name, digest in pin['files'].items())
    SNAP.mkdir(exist_ok=False)
    generated = json.loads((AUTHOR / 'generated-manifest.json').read_text())
    sources = {}
    for name, expected in generated.items():
        path = AUTHOR / 'source' / name
        assert sha(path) == expected
        shutil.copyfile(path, SNAP / name)
        sources[name] = {'source': str(path), 'sha256': expected}
    assert sha(ORIGINAL / 'IndexRoute.lean') == generated['IndexRoute.lean']
    for name, old, new in [('FalseCount','singletonEnums.length = 2','singletonEnums.length = 1'),('FalseCharge','singletonClosed.length = 1','singletonClosed.length = 0'),('FalseCollision','collisionLeft = collisionRight','collisionLeft ≠ collisionRight')]:
        source = (SNAP / (name + '.lean')).read_text()
        assert source.count(old) == 1
        (SNAP / (name + 'Clean.lean')).write_text(source.replace(old, new))
    (SNAP / 'MalformedImport.lean').write_text('import MissingFreshIndexReviewImport\nexample : (0 : Nat) = 1 := by decide\n')
    probe = HERE / 'ConsumerProbe.lean'
    shutil.copyfile(probe, SNAP / probe.name)
    scans = {}
    for path in SNAP.glob('*.lean'):
        code = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
        code = re.sub(r'--[^\n]*', '', code)
        scans[path.name] = re.findall(r'\b(?:sorry|sorryAx|admit|native_decide|axiom|unsafe|implemented_by)\b', code)
    assert all(not bad for bad in scans.values()), scans
    (HERE / 'SOURCE-MANIFEST.json').write_text(json.dumps({'sources':sources,'source_forbidden_tokens':scans,'index_original_sha256':sha(ORIGINAL/'IndexRoute.lean'),'report_sha256':sha(ORIGINAL/'REPORT.md'),'controls_sha256':sha(ORIGINAL/'controls.json')},indent=2)+'\n')
    version = subprocess.check_output([str(ROOT/'bootloops-lean'),'--version'],cwd=SNAP,env=ENV,text=True)
    assert 'version 4.35.0' in version, version
    (RESULTS/'triple-family-transitions-fresh-index-version.log').write_text(version)
    rows = []
    for name in ['TripleDP','ConnectedRegions','FamilyAssembly','IndexRoute','FrozenPositives','CleanTwins']:
        rows.append(positive(name))
    indexrow = next(row for row in rows if row['module']=='IndexRoute')
    assert indexrow['actual_query_count']==28
    assert set(indexrow['axioms'])=={'propext','Quot.sound'}
    for name, statement in [('FalseCount','singletonEnums.length = 2'),('FalseCharge','singletonClosed.length = 1'),('FalseCollision','collisionLeft = collisionRight')]:
        row, log = execute(name,False)
        assert row['returncode'] != 0
        assert 'Tactic `decide` proved that the proposition' in log and '\n  '+statement+'\nis false' in log, log
        assert not re.search(r'unknown module|failed to load|object file|unknown constant',log,flags=re.I),log
        row['negative_kind']='exact false proposition'
        rows.append(row)
        rows.append(positive(name+'Clean'))
    row, log = execute('MalformedImport',False)
    assert row['returncode'] != 0 and 'MissingFreshIndexReviewImport' in log and 'is false' not in log
    row['negative_kind']='import failure excluded from mathematical evidence'
    rows.append(row)
    rows.append(positive('ConsumerProbe'))
    assert all(sha(ROOT/name)==digest for name,digest in prior_manifest['files'].items())
    assert all(sha(ORIGINAL.parent/name)==digest for name,digest in pin['files'].items())
    receipt={'scope':'finite-index interfaces and conditional Family consumer only','version':version.strip(),'records':rows,'fresh_lean_positive_cases':5,'fresh_positive_statements':10,'false_controls':3,'separate_same_import_clean_twins':3,'original_clean_conjunctions':1,'actual_index_queries':28,'prior_completed_review_hashes_unchanged':True,'main_pins_unchanged':True}
    (RESULTS/'triple-family-transitions-fresh-index-lean.json').write_text(json.dumps(receipt,indent=2)+'\n')


if __name__=='__main__': main()
