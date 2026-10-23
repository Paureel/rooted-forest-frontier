#!/usr/bin/env python3
"""Retain post-contact scope witnesses and full own-module axiom checks."""
import hashlib
import json
from pathlib import Path
from replay_sources import compile_one
from audit_origins_v3 import run_audit
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OUT = ROOT / 'research/rmaf/results'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
row = compile_one('ScopeWitnesses')
payload = {'scope': 'post-contact scope counterexamples to stronger readings, not the stated candidate theorems',
           'kernel_witness_row': row, 'all_passed': row['passed'],
           'witnesses': ['embedding guard required', 'normalization owner converse unavailable',
                         'zero budget local success without output', 'one mixed target singleton not both',
                         'local origin guards without original reachability', 'separate generate proper-label guard'],
           'additional_independent_replications': 0}
if row['passed']:
    audit, entries = run_audit('FreshEvidenceOriginAudit', ['FreshComparisons', 'ScopeWitnesses'],
                               ['FreshComparisons', 'ScopeWitnesses'])
    allowed = {'propext','Classical.choice','Quot.sound'}
    bad = [r for r in entries if not set(r['axioms']) <= allowed or r['kind'] == 'axiom']
    payload.update({'own_evidence_audit': audit, 'own_evidence_origin_entries': entries,
                    'own_evidence_axiom_violations': bad,
                    'all_passed': audit['passed'] and not bad})
payload['source_sha256'] = sha(Path(__file__))
dest = OUT / 'algorithm-integration-fresh-review-scope-witnesses-v1.json'
assert not dest.exists()
dest.write_text(json.dumps(payload, indent=2) + '\n')
print(json.dumps({'all_passed': payload['all_passed'], 'scope_witnesses': len(payload['witnesses'])}))
raise SystemExit(0 if payload['all_passed'] else 1)
