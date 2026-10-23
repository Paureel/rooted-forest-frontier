#!/usr/bin/env python3
"""One-shot author emitall and actual original-cut payment controls."""
from pathlib import Path
import subprocess,json,datetime
import local
D=Path(__file__).resolve().parent;R=D.parents[4]
O=R/'results'/('algorithm-universal233-rule5-local-claims-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir()
spec=json.loads((D/'claims-v1.json').read_text());bad=json.loads(json.dumps(spec));bad['claims'][0]['quoted']='79'
(O/'wrong-count-spec.json').write_text(json.dumps(bad,indent=2)+'\n')
for name,path,want in [('clean',D/'claims-v1.json',0),('wrong-count',O/'wrong-count-spec.json',1)]:
 p=subprocess.run([str(R/'bootloops-python'),str(R/'bootloops/tools/emitall/run.py'),str(path),'--out',str(O/(name+'.json'))],cwd=R,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (O/(name+'.log')).write_text(p.stdout);assert p.returncode==want,(name,p.stdout)
 if name=='wrong-count':
  report=json.loads((O/(name+'.json')).read_text())
  assert report['findings_count']==1 and report['FINDINGS'][0]['kind']=='mismatch'
t,s,_=local.fixture_family()['six'];C=local.classify(t,s);b=local.branches(t,s,C)[-1]
def payment(branch,paid):
 assert len(branch['cuts'])==paid and len(branch['partition'])==paid+1,'ACTUAL_ORIGINAL_CUT_PAYMENT_MISMATCH'
 assert local.cut_partition(t,branch['cuts'])==branch['partition']
payment(b,3)
try:payment(b,2)
except AssertionError:paid_false='CAUGHT'
else:raise AssertionError('UNPAID_CUT_SURVIVED')
(O/'certificate.json').write_text(json.dumps(dict(status='PASS_AUTHOR_CLAIMS_CONTROLS',clean_claims=16,wrong_count='CAUGHT',actual_branch=b,unpaid_actual_source_cut=paid_false,post_contact=True),indent=2)+'\n')
(D/'CLAIMS-CONTROLS-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R))),indent=2)+'\n')
print('PASS_AUTHOR_CLAIMS_CONTROLS',O)
