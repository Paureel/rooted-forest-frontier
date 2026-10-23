#!/usr/bin/env python3
"""Retain exact emitall inventory claims and a wrong-count plant."""
from pathlib import Path
import subprocess,json,datetime
D=Path(__file__).resolve().parent;R=D.parents[4]
if (D/'FINAL-CLASSIFICATION-MANIFEST-v1.json').exists():raise SystemExit('FROZEN_NO_WRITE_BOUNDARY')
latest=json.loads((D/'LATEST-REPLAY-v1.json').read_text());cert=json.loads((R/latest['receipt']/'certificate.json').read_text())
pre=json.loads((D/'PREPROOF-RECEIPT-v1.json').read_text());pc=json.loads((R/pre['receipt']/'certificate.json').read_text())
values=[('isolated source modules',cert['source_builds'],"f('r','/source_builds')"),
 ('stored producer occurrences',cert['stored_producer_occurrences'],"f('r','/stored_producer_occurrences')"),
 ('explicit finite orientation controls',len(pc['rows']),"len(f('p','/rows'))")]
for key in ['Rule5FalsePreControls','Rule5FalseGraphControls','ClassificationFalseControls','FinalFalseControls']:
 values.append((key+' rejected',cert['controls'][key]['rejected'],"f('r','/controls/"+key+"/rejected')"))
(D/'REPLAY-SUMMARY-v1.md').write_text('# Author replay inventory\n\n'+''.join('- '+n+': '+str(v)+'\n' for n,v,_ in values)+
 '\nThese counts inventory retained checks. They are not scientific progress percentages.\nAll main milestones remain OPEN; independent credit0.\n')
spec=dict(campaign='OPEN ordinary Rule5 structural classifier author release',base=str(R),
 quote_source=str((D/'REPLAY-SUMMARY-v1.md').relative_to(R)),
 receipts=dict(r=dict(path=latest['receipt']+'/certificate.json'),p=dict(path=pre['receipt']+'/certificate.json')),
 defaults=dict(mode='exact'),claims=[dict(label=n,quoted=str(v),expr=e) for n,v,e in values])
(D/'claims-v1.json').write_text(json.dumps(spec,indent=2)+'\n')
out=R/'results'/('algorithm-universal233-rule5-final-classification-claims-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));out.mkdir()
bad=json.loads(json.dumps(spec));bad['claims'][0]['quoted']=str(cert['source_builds']+1)
(out/'wrong-count-spec.json').write_text(json.dumps(bad,indent=2)+'\n')
for name,path,want in [('clean',D/'claims-v1.json',0),('wrong-count',out/'wrong-count-spec.json',1)]:
 p=subprocess.run([str(R/'bootloops-python'),str(R/'bootloops/tools/emitall/run.py'),str(path),'--out',str(out/(name+'.json'))],cwd=R,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (out/(name+'.log')).write_text(p.stdout);assert p.returncode==want,(name,p.stdout)
 if name=='wrong-count':
  report=json.loads((out/(name+'.json')).read_text());assert report['findings_count']==1 and report['FINDINGS'][0]['kind']=='mismatch'
(out/'certificate.json').write_text(json.dumps(dict(status='PASS_AUTHOR_EMITALL_COUNTS',clean_claims=len(values),wrong_count='CAUGHT',post_contact=True),indent=2)+'\n')
(D/'CLAIMS-CONTROLS-v1.json').write_text(json.dumps(dict(receipt=str(out.relative_to(R))),indent=2)+'\n')
print('PASS_AUTHOR_EMITALL_COUNTS',out)
