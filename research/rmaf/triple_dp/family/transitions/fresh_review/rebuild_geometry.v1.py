#!/usr/bin/env python3
"""One-shot fresh geometry route replay using the reviewer-owned compiler runner."""
import importlib.util
import json
import pathlib
import re
import shutil

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('fresh_main_build', HERE / 'rebuild_main.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
m.SNAP = HERE / 'geometry_snapshot'
m.SNAP.mkdir(exist_ok=False)
m.RESULT = HERE / 'geometry_logs'
m.RESULT.mkdir(exist_ok=False)
m.ENV['LEAN_PATH'] = str(m.SNAP)
source = HERE.parent / 'geometry_route'
author_snapshot = m.ROOT / 'research/rmaf/results/triple-family-transitions-geometry-20261014T141457397535Z/source'
modules = m.MODULES[:3] + [(name, source / (name + '.lean')) for name in ['GeometrySupportDefs', 'GeometryPositive', 'GeometryFalseRoot', 'GeometryFalseBranch', 'MergeGeometry']]
manifest = []
for name, path in modules:
    shutil.copyfile(path, m.SNAP / (name + '.lean'))
    manifest.append({'name': name, 'original': str(path), 'sha256': m.digest(path), 'matches_author_final_snapshot': m.digest(path) == m.digest(author_snapshot / (name + '.lean'))})
assert all(row['matches_author_final_snapshot'] for row in manifest)
for name, old, new in [('GeometryFalseRoot', 'example : ¬ jointSupport', 'example : jointSupport'), ('GeometryFalseBranch', 'example : jointSupport', 'example : ¬ jointSupport')]:
    body = (m.SNAP / (name + '.lean')).read_text()
    assert body.count(old) == 1
    (m.SNAP / (name + 'Clean.lean')).write_text(body.replace(old, new))
# Token scanning here excludes Lean comments so words describing prohibitions do not count as code.
for path in m.SNAP.glob('*.lean'):
    text = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    assert not re.search(r'\b(?:sorry|sorryAx|admit|native_decide|axiom|unsafe|implemented_by)\b', text), path
(HERE / 'geometry-source-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
records = []
for name, _ in modules:
    record, log = m.run(name, not name.startswith('GeometryFalse'))
    records.append(record)
    if name.startswith('GeometryFalse'):
        assert record['exit_code'] != 0
        assert 'Tactic `decide` proved that the proposition' in log and 'is false' in log
        if name == 'GeometryFalseRoot': assert '¬jointSupport singletonRoot singletonRoot []' in log.replace('¬ ', '¬')
        if name == 'GeometryFalseBranch': assert 'jointSupport asymmetricLeft singletonRoot [false, true]' in log
        twin, twinlog = m.run(name + 'Clean', False)
        records.append(twin)
        assert twin['exit_code'] == 0, twinlog
    else:
        assert record['exit_code'] == 0, log
        assert record['actual_query_count'] == len(record['source_queries']), record
        assert set(record['actual_axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}, record
        if name == 'MergeGeometry':
            assert record['actual_query_count'] == 17
            assert set(record['actual_axioms']) == {'propext', 'Quot.sound'}
receipt = {'scope': 'support geometry only; no index/count/cost family construction', 'records': records, 'sources': manifest, 'positive_examples': 7, 'false_controls': 2, 'same_import_clean_twins': 2}
(m.ROOT / 'research/rmaf/results/triple-family-transitions-fresh-geometry.json').write_text(json.dumps(receipt, indent=2)+'\n')
