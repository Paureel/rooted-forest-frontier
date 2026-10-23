#!/usr/bin/env python3
"""Record final paid-billing false twin and clarify raw-list concatenation."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
control = json.loads((HERE / 'paid-scheduler-detector-controls-v2.json').read_text())
assert control['passed'] and len(control['false_twins']) == 2
result = json.loads((HERE / 'REVIEW-RESULT-v3.json').read_text())
result['paid_scheduler_fixture_realization'].update({
    'detector_receipt': 'paid-scheduler-detector-controls-v2.json',
    'undercharged_failure_false_bill': 12,
    'undercharged_failure_caught': True,
})
(HERE / 'REVIEW-RESULT-v4.json').write_text(json.dumps(result, indent=2) + '\n')
report = (HERE / 'REVIEW-REPORT-v3.md').read_text()
report = report.replace('the false own-minimum-discount trace [2,0] is rejected.',
                        'the false own-minimum-discount trace [2,0] and false failed-call bill of 12 are rejected.')
report = report.replace('`WORK-RULING-v1.md`', '`WORK-RULING-v2.md`')
(HERE / 'REVIEW-REPORT-v4.md').write_text(report)
work = (HERE / 'WORK-RULING-v1.md').read_text()
old = 'both full raw lists have costs `[1,2,2]`'
assert work.count(old) == 1
work = work.replace(old, 'the concatenation of both full raw lists has costs `[1,2,2]`')
(HERE / 'WORK-RULING-v2.md').write_text(work)
ledger = json.loads((HERE / 'CONTACT-LEDGER-v3.json').read_text())
ledger['new_post_contact_checks'].append('same retained scalar observations: wrong trace and failed-call undercharge mutations both caught; no further Lean run')
(HERE / 'CONTACT-LEDGER-v4.json').write_text(json.dumps(ledger, indent=2) + '\n')
notes = (HERE / 'INSTRUMENT-NOTES-v2.md').read_text()
notes += '\n`check_paid_scheduler_v2.py` qualifies the scalar comparison detector on the retained four actual rows, with a known clean/failed-call plant first, then both wrong-budget and failed-call-undercharge corrupt twins. It preserves all Lean receipts and moves no original expectation.\n'
(HERE / 'INSTRUMENT-NOTES-v3.md').write_text(notes)
with (HERE / 'WORKFILE-v1.md').open('a') as f:
    f.write('''

Final paid detector qualification passed a known clean/failed-call plant before all four retained actual rows and two corrupt twins. It caught both wrong [2,0] query calls and an undercharged failed-call bill of 12 instead of 25; no further Lean execution or case-count increase occurred. WORK-RULING-v2 clarifies that [1,2,2] belongs to the concatenation of both raw lists. Final report/result and contact ledger are v4; all earlier drafts remain. A bounded 16/64 MiB streaming-hash pilot measured 0.01046/0.031995 s, projecting under 37 s at ten times the slower measured per-byte rate for approximately 5.90 GB. The final hash pass is integrity I/O only, with no scientific runtime inference.
''')
print(json.dumps({'report': 'REVIEW-REPORT-v4.md', 'result': 'REVIEW-RESULT-v4.json', 'paid_false_twins': 2}))
