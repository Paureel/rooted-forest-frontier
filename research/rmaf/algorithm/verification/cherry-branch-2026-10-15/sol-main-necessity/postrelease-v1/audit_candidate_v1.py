#!/usr/bin/env python3
"""Apply the unchanged, prerelease-planted stored-producer instrument to release."""
import argparse, hashlib, importlib.util,json,os,sys,time
from pathlib import Path
P=Path(__file__).resolve().parent; BEFORE=P.parent
sys.path.insert(0,str(BEFORE))
import origin_gate_v3 as instrument
def main():
    ap=argparse.ArgumentParser(); ap.add_argument('mode',choices=['pilot','full']); a=ap.parse_args()
    data=json.loads((P/'source-inventory-v2.json').read_text()); by={x['module']:x for x in data['sources']}
    names=['RMAF'] if a.mode=='pilot' else data['topological_order']
    for n in names: assert instrument.sha(P/'sources'/(n+'.lean'))==by[n]['sha256']
    records=[]; label='candidate-audit-'+a.mode+'-run1'; at=time.perf_counter()
    r=instrument.run(['--run',str(BEFORE/'origin/ProducerAudit_v1.lean')]+names,P/'sources',P/'build',str(P/label),records)
    assert r.returncode==0,('candidate audit execution failed',r.stdout[-2000:])
    obj=json.loads(r.stdout)
    for row in obj['rows']:
        row['type_sha256']=hashlib.sha256(row['type'].encode()).hexdigest()
        row['body_sha256']=None if row['body'] is None else hashlib.sha256(row['body'].encode()).hexdigest()
    (P/(label+'.json')).write_text(json.dumps(obj,indent=2)+'\n')
    imports={n:['Init','Init']+by[n]['imports'] for n in names}
    instrument.gate(obj,names,imports)
    result={'status':'PRODUCER_GATE_PASS','modules':len(names),'occurrences':len(obj['rows']),'unique_names':len({r['name'] for r in obj['rows']}),'axioms':sorted({v for r in obj['rows'] for v in r['axioms']}),'direct_axioms':[r['name'] for r in obj['rows'] if r['kind']=='axiom'],'missing_refs':[r['name'] for r in obj['rows'] if r['missing']],'commands':records,'seconds':time.perf_counter()-at,'instrument_sha256':instrument.sha(BEFORE/'origin/ProducerAudit_v1.lean'),'unchanged_instrument':True,'scientific_oleans_copied':0}
    (P/(label+'-summary.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='commands'}))
if __name__=='__main__': main()
