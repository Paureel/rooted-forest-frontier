"""Seal only owned preparation artifacts; never author sources or old receipts."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    for name in ('CONTROL-FREEZE-v1.json','CONTROL-FREEZE-v2.json','TOY-FREEZE-v2.json'):
        m=json.loads((HERE/name).read_text())
        for row in m['files']:assert sha(ROOT/row['path'])==row['sha256'],row['path']
    prior=json.loads((HERE/'PRIOR-PRESERVATION-v1.json').read_text())
    for row in prior['previous_frozen_checks']:
        p=ROOT/row['manifest'];assert sha(p)==row['sha256']
        m=json.loads(p.read_text());assert len(m['files'])==row['files']
        for f in m['files']:assert sha(ROOT/f['path'])==f['sha256'],f['path']
    base=ROOT/'research/rmaf/results'
    names=['algorithm-kept-parent-prerelease-pilot-v1.json','algorithm-kept-parent-prerelease-full-v1.json','algorithm-kept-parent-prerelease-pilot-v2.json','algorithm-kept-parent-prerelease-full-v2.json','algorithm-kept-parent-prerelease-toy-gates-v2.json']
    results=[base/x for x in names]
    receipts=[json.loads(p.read_text()) for p in results]
    assert receipts[1]['status']=='FAIL_RETAINED'
    assert all(r['status'].startswith('PASS_') for i,r in enumerate(receipts) if i!=1)
    assert receipts[3]['fixtures']==11 and receipts[3]['budget_cases']==20 and receipts[3]['positive_checks']==203 and receipts[3]['negative_catches']==30
    assert receipts[4]['negative_custom_axiom_catches']==3 and receipts[4]['explicit_false_prop_catches']==1
    files=sorted([p for p in HERE.rglob('*') if p.is_file() and '__pycache__' not in p.parts and not p.name.startswith('READY-MANIFEST-')]+results)
    assert len(files)==len(set(files))
    rows=[{'path':str(p.relative_to(ROOT)),'realpath':str(p.resolve()),'sha256':sha(p),'bytes':p.stat().st_size} for p in files]
    old=json.loads((HERE/'CONTROL-FREEZE-v1.json').read_text())
    external=[r for r in old['files'] if not str(ROOT/r['path']).startswith(str(HERE)+'/')]
    manifest={'version':1,'stage':'READY_PRE_CANDIDATE','utc':datetime.now(timezone.utc).isoformat(),'immutable':True,'candidate_contact':False,'candidate_compilation':False,'root_release_pending':True,'preparation_children':0,'author_contacts':0,'all_main_milestones':'OPEN','replication_count_added':0,'input_expectations_frozen_before_execution':True,'versioned_preparation_corrections':['CORRECTION-v2.md','TOY-CORRECTION-v2.md'],'earlier_failures_retained':True,'scope':'finite source/parent/all-output/restriction preparation only; candidate theorem, original cut lifting and query discount not accepted','receipts':[{'path':str(p.relative_to(ROOT)),'sha256':sha(p),'status':r['status']} for p,r in zip(results,receipts)],'prior_preservation':prior['previous_frozen_checks'],'external_input_pins':external,'files':rows,'file_count':len(rows),'total_bytes':sum(r['bytes'] for r in rows)}
    out=HERE/'READY-MANIFEST-v1.json';assert not out.exists();out.write_text(json.dumps(manifest,indent=2)+'\n')
    for p in files:
        if p!=HERE/'TARGET-v1.md':p.chmod(0o444)
    out.chmod(0o444)
    print(json.dumps({'manifest':str(out.relative_to(ROOT)),'sha256':sha(out),'files':len(rows),'bytes':manifest['total_bytes'],'status':manifest['stage']}))
if __name__=='__main__':main()
