#!/usr/bin/env python3
"""One-shot report-count transcription spec; scientific derivation stays in receipts."""
from copy import deepcopy
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
OUT = ROOT / 'research/rmaf/results'
paths = {
 'p': HERE/'CANDIDATE-PIN.json', 'r': HERE/'READY-ARTIFACTS.json',
 'c': OUT/'algorithm-integration-fresh-review-controls-v1.json',
 's': OUT/'algorithm-integration-fresh-review-source-replay-v1.json',
 'a': HERE/'AXIOM-INVENTORY.json',
 'f': OUT/'algorithm-integration-fresh-review-comparisons-v1.json',
 'k': OUT/'algorithm-integration-fresh-review-origin-audit-v3.json',
 'w': OUT/'algorithm-integration-fresh-review-scope-witnesses-v2.json',
 'h': OUT/'algorithm-integration-fresh-review-hostile-semantics-20261015.json',
 'l': HERE/'PRE-CANDIDATE-RECEIPT.json'}
claims = [
 ('author immutable files', '72', "len(f('p','/rows'))"),
 ('readiness entries preserved', '26', "len(f('r','/file_hashes'))"),
 ('clean controls', '49', "f('c','/clean_passed')"),
 ('false expected twins caught', '49', "f('c','/false_expectations_caught')"),
 ('positive frozen modules', '18', "f('s','/positive_modules')"),
 ('module-origin declarations', '1415', "f('a','/total_originating_declarations')"),
 ('private declarations', '144', "len(f('a','/private_declarations'))"),
 ('names beyond author explicit inventory', '966', "len(f('a','/additional_to_author_explicit_inventory'))"),
 ('author explicit inventory matched', '449', "len(f('a','/author449_comparison'))"),
 ('finite compiled assertions', '76', "f('f','/assertions')"),
 ('controls with executable fields', '30', "f('f','/controls_with_compiled_fields')"),
 ('author explicit false diagnostics', '3', "f('s','/rows/18/explicit_false_diagnostics')"),
 ('fresh explicit false diagnostics', '2', "f('f','/rows/1/explicit_false_diagnostics')"),
 ('detector explicit false diagnostics', '1', "f('k','/kernel_plant_rows/2/explicit_false_diagnostics')"),
 ('total explicit false diagnostics', '6', "f('s','/rows/18/explicit_false_diagnostics')+f('f','/rows/1/explicit_false_diagnostics')+f('k','/kernel_plant_rows/2/explicit_false_diagnostics')"),
 ('post-contact source-model witnesses', '5', "len(f('h','/witnesses'))"),
 ('actual-code scope witnesses', '6', "len(f('w','/witnesses'))"),
 ('extra independent replications', '0', "f('l','/additional_independent_replications')")]
spec = {'campaign': 'integration review reported integer counts only; no scientific re-evaluation',
        'quote_source': str(HERE/'VERDICT.md'), 'defaults': {'mode':'exact'},
        'receipts': {alias:{'path':str(p)} for alias,p in paths.items()},
        'claims': [{'label':label,'quoted':quoted,'expr':expr} for label,quoted,expr in claims]}
(HERE/'CLAIMS.json').write_text(json.dumps(spec,indent=2)+'\n')
false = deepcopy(spec)
false['campaign'] = 'deliberately corrupt report count; expected mismatch and exit1'
false['claims'] = [{'label':'wrong clean-control count','quoted':'50','expr':"f('c','/clean_passed')"}]
(HERE/'CLAIMS-FALSE.json').write_text(json.dumps(false,indent=2)+'\n')
print(json.dumps({'report_counts':len(claims),'false_count_twin':1}))
