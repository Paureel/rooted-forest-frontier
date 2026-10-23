from pathlib import Path
import json,hashlib
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent
ps=[root/'research/rmaf/results'/('algorithm-query-classifier-fresh-review-'+s+'.json') for s in ['pilot-v2','size-pilot-v2']];rows=[r for p in ps for r in json.loads(p.read_text())['rows']];slow=max(r['seconds'] for r in rows);n=json.loads((b/'CONTROL-PIN.json').read_text())['declared_controls']
x={'scope':'fixed35-case readiness battery only;no census/source runtime inference','measured_cases':len(rows),'slowest_case_seconds':slow,'fixed_cases':n,'conservative_projection_seconds':slow*n,'pilot_hashes':{str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in ps},'decision':'run fixed battery only','failed_V1_pilot_not_used_for_projection':True};(b/'PILOT-PROJECTION.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
