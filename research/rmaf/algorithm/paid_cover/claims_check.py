#!/usr/bin/env python3
"""One-shot final count/provenance sweep, not scientific acceptance."""
from pathlib import Path
import json
import hashlib
HERE = Path(__file__).resolve().parent
OUT = HERE.parents[1]/'results'
report = (HERE/'REPORT.md').read_text()
controls = json.loads((OUT/'algorithm-cover-controls-v1.json').read_text())['result']
pilot = json.loads((OUT/'algorithm-cover-frontier-pilot-v2.json').read_text())['result']
bounded = json.loads((OUT/'algorithm-cover-frontier-bounded-v2.json').read_text())['result']
full = json.loads((OUT/'algorithm-cover-full-pilot-v3.json').read_text())
cover = full['five_leaf_failed_minimum_cover_repaired']['cover']
audit = json.loads((OUT/'algorithm-cover-lean-audit-v2.json').read_text())
assert controls['passed'] == controls['total'] == 27
assert pilot['pairs'] == 20 and bounded['pairs'] == 54
assert bounded['witness']['optimum_cuts'] == 2
assert [c['paid_total'] for c in bounded['witness']['children']] == [3,3]
assert cover['cutsets_tested'] == 37 and cover['prefilter_states'] == 17
assert len(cover['states']) == 10 and cover['coarsening_scans'] == 180
assert cover['paid_vector'] == [1,1]+[2]*8
assert cover['exact_mass'] == '126200/53361'
assert audit['theorems'] == 10 and audit['false_control_rejected']
assert audit['axioms'] == ['Classical.choice','Quot.sound','propext']
for token in ['27-control','20-case','54 compared','37 precut','17 distinct',
              '180 coarsening','126200/53361','ten statements','four exact integer']:
    assert token in report,token
result = dict(status='report-counts-match-retained-receipts',
              receipt_assertion_groups=10,report_tokens_checked=9,
              proof_claim_scope='finite executable model only',
              prose_checks=['sentence meaning and scope','two style/number passes',
                            'all quoted local source statements checked at named locators'],
              report_sha256=hashlib.sha256(report.encode()).hexdigest(),
              acceptance='This reporting check supplies no algorithm correctness or exponent theorem.')
dest = OUT/'algorithm-cover-report-check-v2.json'
assert not dest.exists(),dest
dest.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(output=str(dest),status=result['status'])))
