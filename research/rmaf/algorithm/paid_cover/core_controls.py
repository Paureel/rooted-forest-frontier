#!/usr/bin/env python3
"""One-shot supplementary split-core controls; finite development only."""
from pathlib import Path
import hashlib
import json
import time
from cover_solver import (parse_state, select_core, core_children, solve,
                          source_realization, Tree, mass)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = json.loads((HERE/'core-control-spec-v1.json').read_text())
started = time.perf_counter()
rows = []
for name in ('two_color','three_color'):
    fixture = spec[name]
    target,sources = parse_state(fixture['target'],fixture['source'],fixture['minimum_additional_cuts'])
    core = select_core(target,sources)
    assert core is not None
    children = core_children(sources,core)
    assert sorted(x['charge'] for x in children) == fixture['core_paid_vector_sorted']
    for child in children:
        assert child['charge'] == sum(len(p['realization']['edges']) for p in child['history'])
    fail = solve(fixture['target'],fixture['source'],fixture['minimum_additional_cuts']-1)
    good = solve(fixture['target'],fixture['source'],fixture['minimum_additional_cuts'])
    assert not fail['feasible'] and good['feasible']
    assert good['additional_cuts'] == fixture['minimum_additional_cuts']
    rows.append(dict(name=name, core=core,children=children,lower_budget=fail,
                     exact_budget=good,mass_at_2_31=str(mass(x['charge'] for x in children))))
constructed = Tree(((spec['three_color']['source'][0],spec['three_color']['source'][1]),spec['three_color']['source'][2]))
forest_parts = [Tree(s).labels for s in spec['three_color']['source']]
origin = source_realization(constructed,forest_parts,2)
assert origin is not None
child = rows[1]['children'][0]
caught = False
try:
    assert child['charge']-1 == sum(len(p['realization']['edges']) for p in child['history'])
except AssertionError:
    caught = True
assert caught
report = dict(status='supplementary-finite-controls',rows=rows,
              three_color_source_tree=constructed.syntax,source_cut_certificate=origin,
              false_charge_corruption_caught=caught,elapsed_seconds=time.perf_counter()-started,
              hashes={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in
                      [Path(__file__),HERE/'core-control-spec-v1.json',HERE/'cover_solver.py']},
              scope=spec['scope'])
dest = ROOT/'results'/'algorithm-cover-core-controls-v1.json'
assert not dest.exists(),dest
dest.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(output=str(dest),states=2,corruption_caught=caught,
                      vectors=[r['mass_at_2_31'] for r in rows],elapsed_seconds=report['elapsed_seconds'])))
