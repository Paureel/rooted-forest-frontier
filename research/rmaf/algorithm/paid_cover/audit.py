#!/usr/bin/env python3
"""One-shot axiom audit of already compiled finite counterexample plus false twin.
Route-author audit, not fresh nonauthor reconstruction or graph certification.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = HERE.parents[1]/'results'
env = dict(os.environ, LEAN_PATH=str(HERE))
expected = ['proper_labels','initial_outside_terminal','exact_one_cut_class_filter',
            'parent_two_cut_witness','exact_parent_and_frontier_optima',
            'every_feasible_at_least','first_frontier_loses_every_two_cut_assignment',
            'quartet_five_children_fail_paid_mass','compatible_two_color_mass_passes',
            'unpaid_query_has_no_strict_budget_decrease']
started = time.perf_counter()
positive = subprocess.run([str(ROOT/'bootloops-lean'),str(HERE/'Audit.lean')],
                          env=env,cwd=ROOT,text=True,capture_output=True)
log = positive.stdout+positive.stderr
dest = OUT/'algorithm-cover-lean-axioms-v2.log'
assert not dest.exists(), dest
dest.write_text(log)
assert positive.returncode == 0, log
assert all('PaidCoverFailedFrontier.'+x in log for x in expected), log
used = set()
for names in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',log):
    used.update(x.strip() for x in names.split(',') if x.strip())
assert used <= {'propext','Classical.choice','Quot.sound'}, used
sources = [HERE/'FailedFrontier.lean',HERE/'Audit.lean',HERE.parents[1]/'lean'/'RMAF.lean']
for source in sources:
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.read_text()), source
negative = subprocess.run([str(ROOT/'bootloops-lean'),str(HERE/'FalseFrontier.lean')],
                          env=env,cwd=ROOT,text=True,capture_output=True)
negative_log = negative.stdout+negative.stderr
dest = OUT/'algorithm-cover-lean-negative-v2.log'
assert not dest.exists(), dest
dest.write_text(negative_log)
assert negative.returncode != 0 and 'false' in negative_log.lower(), negative_log
report = dict(status='route-author-finite-model-audited',theorems=len(expected),
              axioms=sorted(used),false_control_rejected=True,
              elapsed_seconds=time.perf_counter()-started,
              earlier_compilation=dict(RMAF_exit=0,FailedFrontier_exit=0,
                                       retained_olean=True,main_compile_elapsed='not measured to completion'),
              hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sources+[HERE/'FalseFrontier.lean',HERE/'FailedFrontier.olean',HERE/'RMAF.olean']},
              scope='Finite executable-model result only; RMAF graph correspondence and fresh nonauthor replay OPEN.')
dest = OUT/'algorithm-cover-lean-audit-v2.json'
assert not dest.exists(), dest
dest.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(output=str(dest),status=report['status'],theorems=len(expected),
                      false_control_rejected=True,elapsed_seconds=report['elapsed_seconds'])))
