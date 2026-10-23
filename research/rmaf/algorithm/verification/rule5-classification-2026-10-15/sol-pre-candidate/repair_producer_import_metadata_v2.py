#!/usr/bin/env python3
"""Versioned representation correction; all mathematical expectations preserved."""
import hashlib
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
old = json.loads((HERE/'PRODUCER-EXPECTATIONS-v1.json').read_text())
new = dict(old)
new['literal_stored_imports'] = {'base':['Init','Init','Std'], 'adapted':['Init','Init','ClassEmpty']}
new['representation_amendment'] = 'Lean stored import metadata includes two automatic Init entries; v1 incorrectly expected only the written source import. Preserve all entries and compare exactly.'
(HERE/'PRODUCER-EXPECTATIONS-v2.json').write_text(json.dumps(new,indent=2)+'\n')
script = (HERE/'producer_controls_v1.py').read_text()
script = script.replace('PRODUCER-EXPECTATIONS-v1.json','PRODUCER-EXPECTATIONS-v2.json')
script = script.replace('PRODUCER-CONTROLS-PIN-v1.json','PRODUCER-CONTROLS-PIN-v2.json')
script = script.replace("'-v1.json'", "'-v2.json'")
script = script.replace("base['producer_counts'][0]['imports'] == ['Std']", "base['producer_counts'][0]['imports'] == SPEC['literal_stored_imports']['base']")
script = script.replace("adapted['producer_counts'][0]['imports'] == ['ClassEmpty']", "adapted['producer_counts'][0]['imports'] == SPEC['literal_stored_imports']['adapted']")
(HERE/'producer_controls_v2.py').write_text(script)
pin = json.loads((HERE/'PRODUCER-CONTROLS-PIN-v1.json').read_text())
pin['entries'] = [r for r in pin['entries'] if r['path'] != 'PRODUCER-EXPECTATIONS-v1.json']
p = HERE/'PRODUCER-EXPECTATIONS-v2.json'
pin['entries'].append({'path':p.name,'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
pin['preserved_previous_pin'] = 'PRODUCER-CONTROLS-PIN-v1.json'
(HERE/'PRODUCER-CONTROLS-PIN-v2.json').write_text(json.dumps(pin,indent=2)+'\n')
p.chmod(0o444);(HERE/'PRODUCER-CONTROLS-PIN-v2.json').chmod(0o444)
failure = json.loads((HERE/'producer-battery-v1.json').read_text())
assert not failure['passed']
(HERE/'PRODUCER-PREPARATION-FAILURE-v1.json').write_text(json.dumps({
    'candidate_contact':False,'failed_receipt':'producer-battery-v1.json',
    'failure_layer':'instrument import-metadata expectation',
    'completed_commands':len(failure['commands']),'completed_gates':len(failure['gates']),
    'expected_v1':['Std'],'actual_base':['Init','Init','Std'],
    'actual_adapted':['Init','Init','ClassEmpty'],
    'mathematical_controls_changed':False,'auditor_changed':False,
    'correction':'literal stored import metadata pinned in v2; rerun pilot before battery',
},indent=2)+'\n')
with (HERE/'WORKFILE-v1.md').open('a') as f:
    f.write('''

## Increment 4: preserved producer import-metadata failure
Producer battery v1 stopped after 18 successful measured commands and 10 completed clean/corruption gates. Its exact semantic import-adapter record comparison passed; the subsequent assertion incorrectly expected the stored imports to equal only the written import. Actual stored metadata is [Init, Init, Std], or [Init, Init, ClassEmpty] for the literal adapter. The duplicate automatic Init entries are retained. This is an instrument representation expectation failure before any candidate contact, not a candidate theorem failure. v1 sources/logs/receipts/pins remain. v2 separately pins these literal metadata lists, changes no mathematical control or auditor byte, and must pass a new pilot before its battery.
''')
print(json.dumps({'versioned_correction':'literal stored imports','candidate_contact':False}))
