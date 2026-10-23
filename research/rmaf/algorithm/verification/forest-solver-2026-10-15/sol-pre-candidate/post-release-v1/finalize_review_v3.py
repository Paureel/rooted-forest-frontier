#!/usr/bin/env python3
"""Finalize this arm's scoped result, retaining earlier drafts verbatim."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
paid = json.loads((HERE / 'paid-scheduler-controls-full-v1.json').read_text())
rows = json.loads((HERE / 'paid-scheduler-full-v1.json').read_text())
assert paid['passed'] and len(rows) == 4
assert paid['false_own_minimum_discount']['caught']
result = json.loads((HERE / 'REVIEW-RESULT-v2.json').read_text())
result['executed']['actual_paid_scheduler_scalar_cases'] = 4
result['paid_scheduler_fixture_realization'] = {
    'context': 'post-contact scalar realization of frozen paid-scheduler false controls',
    'receipt': 'paid-scheduler-controls-full-v1.json',
    'two_minima_2_q3_calls': [],
    'two_minima_2_q4_calls': [2, 2],
    'second_failure_calls': [2, 2],
    'second_failure_recursive_bill': 25,
    'own_minimum_discount_false_trace': [2, 0],
    'false_trace_caught': True,
    'ordinary_solver_or_new_replication': False,
}
(HERE / 'REVIEW-RESULT-v3.json').write_text(json.dumps(result, indent=2) + '\n')
report = (HERE / 'REVIEW-REPORT-v2.md').read_text()
old = 'The 60 ordinary table pairs are test fixtures.'
new = old + (' Four further scalar cases execute the actual paid scheduler: two minima of 2 refuse at q=3 and issue budgets [2,2] at q=4. A second failed call retains both paid charges (25 fixture units); the false own-minimum-discount trace [2,0] is rejected. These are post-contact fixture realizations of the frozen controls, without a new replication count.')
assert report.count(old) == 1
(HERE / 'REVIEW-REPORT-v3.md').write_text(report.replace(old, new))
ledger = json.loads((HERE / 'CONTACT-LEDGER-v2.json').read_text())
ledger['new_post_contact_checks'] += [
    '15 physical original-basename contexts with fresh aliases and Name-slot-only rule; five false twins',
    'four actual scalar paid-scheduler fixtures after successful measured pilot; wrong own-discount trace caught',
]
ledger['retained_diagnostic_failures'] = (
    'Main report v1 broad identifier spacing caught in self-read and replaced by literal v2 template; '
    'a read-only receipt-summary command assumed all JSON roots were objects and stopped on the '
    '64-row premise list; no scientific input or receipt changed. See DIAGNOSTIC-FAILURES-v1.json.'
)
(HERE / 'CONTACT-LEDGER-v3.json').write_text(json.dumps(ledger, indent=2) + '\n')
notes = (HERE / 'INSTRUMENT-NOTES-v1.md').read_text()
notes += '''

`natural_module_alias_review_v1.py` extends the counterpart compilation to all 15 physical original module basenames that differ from the canonical assembly names. `classify_natural_names_v1.py` applies only the explicitly declared root/import module correspondence inside generated/private Name slots, plus lexical Name formatting; five false twins reject numeric, public, unmarked binder, private-looking literal and annotation edits. Raw differences remain retained.

`paid_scheduler_controls_v1.py` executes the actual generic `meterSchedule` on four scalar job fixtures after a one-row measured pilot. It checks refusal, exact paid query budgets, answer/failure and full failure billing; its wrong own-minimum-discount trace must fail. This post-contact realization does not implement an ordinary-tree solver. The scalar charge units are fixture units and have no primitive runtime interpretation.

`seal_review_v1.py` verifies the unchanged 88-file prerelease seal, required scientific receipts and exact 143-source/fresh-olean digests, then hashes all local review payloads in streaming chunks. It includes failed and uncredited artifacts without promoting them to positive evidence. The manifest binds the scoped reports and root release; byte integrity does not add scientific acceptance beyond the reports.
'''
(HERE / 'INSTRUMENT-NOTES-v2.md').write_text(notes)
(HERE / 'DIAGNOSTIC-FAILURES-v1.json').write_text(json.dumps({
    'context': 'final reporting only; no mathematical gate or candidate mutation',
    'preserved_report_draft': 'REVIEW-REPORT-v1.md',
    'report_correction': 'literal template in write_review_result_v2.py; v3 adds scheduler evidence only',
    'receipt_summary_command': {
        'operation': 'read-only JSON schema/count inspection',
        'error': "AttributeError: 'list' object has no attribute 'items'",
        'cause': 'PREMISE-TRACE-v2.json is a 64-row list',
        'scientific_receipts_modified': False,
        'correction': 'subsequent read explicitly inspected JSON root types',
    },
}, indent=2) + '\n')
with (HERE / 'WORKFILE-v1.md').open('a') as f:
    f.write('''

## Actual paid scheduler and final seal
After a successful one-row pilot (0.779581375001726 s), the fixed four-case scalar scheduler battery passed in 0.7703657919992111 s. Two minima of 2 cause no queries at q=3, then exact budgets [2,2] at q=4. A failed second call keeps both paid charges, 25 fixture units; the deliberately false own-minimum-discount trace [2,0] is caught. This is a post-contact realization of original controls, not a new ordinary solver or replication. No expectation moved.

The final report/result are v3; previous drafts are preserved. Contact ledger v3 includes the 15 original-basename contexts and scalar scheduler realization. Final prose/number self-read checks exact source count, occurrence/name units, every finite denominator, condition-only bill claim and OPEN global/primitive/IR scope. A read-only diagnostic schema-summary command failed on a list-root JSON; the error and correction are recorded separately without changing scientific receipts. Final manifest will bind all local files, including failed preparations and the uncredited large raw outputs, using streaming hashes and stable file metadata. Original READY and all 143 fresh source/output digests must verify before sealing.
''')
print(json.dumps({'report': 'REVIEW-REPORT-v3.md', 'result': 'REVIEW-RESULT-v3.json', 'paid_cases': 4}))
