#!/usr/bin/env python3
"""Retain the detected raw-output naming limitation and isolate the final rerun."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
script=(HERE/'producer_controls_v2.py').read_text()
assert "-occurrences-v1.json" in script
script=script.replace('-occurrences-v1.json','-occurrences-v3.json').replace("'-v2.json'","'-v3.json'")
needle="OUT = HERE/('producer-'+MODE+'-v3.json')"
assert needle in script
script=script.replace("RESULT = {'context':", "RESULT = {'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'auditor_sha256':hashlib.sha256((HERE/'reused/producer_audit_v4.lean').read_bytes()).hexdigest(), 'context':",1)
target=HERE/'producer_controls_v3.py';assert not target.exists()
target.write_text(script);target.chmod(0o444)
amendment='''# Producer raw-output path amendment

Final preparation bookkeeping found that the v2 driver versioned its main receipt but retained the `-occurrences-v1.json` raw output suffix. Its rerun therefore reused the v1 raw inventory paths. The v1 failed source, log, structured command/gate receipt and metadata-failure explanation remain intact; the exact first-run raw JSON bytes are not independently retained and must not be claimed as such. The surviving v1-named raw inventories belong to the successful v2 rerun. No mathematical expectation, scientific toy source or auditor byte changed, and no classification candidate had been contacted.

This limitation is preserved explicitly. Driver v3 uses distinct raw inventory and main receipt paths and records the actual driver/auditor digests in its receipts. It retains the exact v2 expectations and all earlier artifacts. A new measured pilot must pass before the fixed battery reruns. Final positive detector credit comes from the separately named v3 outputs. This corrects evidence naming; it does not restore missing first-run raw-byte provenance or grant extra replication credit.
'''
(HERE/'PRODUCER-OUTPUT-PATH-AMENDMENT-v3.md').write_text(amendment)
with (HERE/'WORKFILE-v1.md').open('a') as f:
    f.write('''

## Increment 11: raw-output naming limitation found before READY
Final bookkeeping found that producer v2 versioned its main receipt but retained the v1 raw occurrence suffix, reusing those raw paths. The failed v1 source/log/structured receipt and exact import-failure explanation remain; first-run raw JSON bytes are not independently retained. The v1-named raw inventories now belong to the successful v2 run. This is disclosed in PRODUCER-OUTPUT-PATH-AMENDMENT-v3.md, without claiming full original raw-byte preservation. No candidate classification contact, math expectation or auditor change occurred. Final driver v3 uses distinct raw/receipt names and records its driver/auditor digests; rerun its tiny pilot before the same fixed20-command/18-gate battery. Earlier artifacts remain intact and receive no extra replication count.
''')
print(json.dumps({'version':'v3','scope':'unique output paths; unchanged controls/auditor','candidate_contact':False}))
