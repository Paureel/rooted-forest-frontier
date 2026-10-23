from pathlib import Path
import json,hashlib
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent
files=[root/'research/rmaf/results'/('algorithm-whole-source-work-fresh-review-'+n+'.json') for n in ['pilot-v1','size-pilot-v1']]
rows=[row for p in files for row in json.loads(p.read_text())['rows']];slow=max(x['seconds'] for x in rows);count=json.loads((b/'CONTROL-PIN.json').read_text())['declared_controls']
x={'scope':'Fixed34-case readiness battery, no census projection or source-runtime inference','pilot_case_count':len(rows),'slowest_measured_case_seconds':slow,'case_count':count,'conservative_linear_projection_seconds':slow*count,'pilot_receipt_sha256':{str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},'decision':'run frozen fixed battery; no scale extension','empirical_timing_only_measured_configuration':True}
(b/'PILOT-PROJECTION.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
