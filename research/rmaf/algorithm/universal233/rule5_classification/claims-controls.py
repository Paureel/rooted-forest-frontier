#!/usr/bin/env python3
"""Use the existing emitall instrument for the retained author count claims."""
from pathlib import Path
import subprocess,json,datetime
D=Path(__file__).resolve().parent;R=D.parents[4]
if (D/'CLASSIFICATION-MANIFEST-v1.json').exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
latest=json.loads((D/'LATEST-REPLAY-v1.json').read_text())
large=sorted((R/'results').glob('algorithm-universal233-rule5-classification-large-controls-*'))[-1]
spec=dict(campaign='OPEN ordinary Rule5 classification author prefix',base=str(R),
 quote_source=str((D/'REPLAY-SUMMARY-v1.md').relative_to(R)),
 receipts=dict(r=dict(path=latest['receipt']+'/certificate.json'),l=dict(path=str((large/'certificate.json').relative_to(R)))),
 defaults=dict(mode='exact'),claims=[
 dict(label='isolated source modules',quoted='90',expr="f('r','/source_builds')"),
 dict(label='stored producer occurrences',quoted='3198',expr="f('r','/stored_producer_occurrences')"),
 dict(label='earlier false claims',quoted='4',expr="f('r','/controls/Rule5FalsePreControls/rejected')"),
 dict(label='preceding graph false claims',quoted='2',expr="f('r','/controls/Rule5FalseGraphControls/rejected')"),
 dict(label='new false claims',quoted='8',expr="f('r','/controls/ClassificationFalseControls/rejected')"),
 dict(label='bounded Case1 pair controls',quoted='24',expr="f('l','/control_count')")])
(D/'claims-v1.json').write_text(json.dumps(spec,indent=2)+'\n')
O=R/'results'/('algorithm-universal233-rule5-classification-claims-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir()
bad=json.loads(json.dumps(spec));bad['claims'][0]['quoted']='91'
(O/'wrong-count-spec.json').write_text(json.dumps(bad,indent=2)+'\n')
for name,path,want in [('clean',D/'claims-v1.json',0),('wrong-count',O/'wrong-count-spec.json',1)]:
 p=subprocess.run([str(R/'bootloops-python'),str(R/'bootloops/tools/emitall/run.py'),str(path),'--out',str(O/(name+'.json'))],cwd=R,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (O/(name+'.log')).write_text(p.stdout);assert p.returncode==want,(name,p.stdout)
 if name=='wrong-count':
  report=json.loads((O/(name+'.json')).read_text());assert report['findings_count']==1 and report['FINDINGS'][0]['kind']=='mismatch'
(O/'certificate.json').write_text(json.dumps(dict(status='PASS_AUTHOR_EMITALL_COUNTS',clean_claims=6,wrong_count='CAUGHT',post_contact=True),indent=2)+'\n')
(D/'CLAIMS-CONTROLS-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R))),indent=2)+'\n')
print('PASS_AUTHOR_EMITALL_COUNTS',O)
