"""Seal this completed local scoped review; never mutates released inputs."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,sys
sys.dont_write_bytecode=True
import rebuild as R

def check_manifest(path,pin,field):
    assert R.sha(path)==pin,(path,'manifest pin')
    d=json.loads(path.read_text());rows=d[field]
    for x in rows:
        p=R.ROOT/x['path'];assert p.is_file() and R.sha(p)==x['sha256'],x['path']
        if 'bytes' in x:assert p.stat().st_size==x['bytes'],x['path']
    return {'manifest':str(path.relative_to(R.ROOT)),'sha256':pin,'files':len(rows),'all_match':True}

def main():
    out=R.HERE/'REVIEW-MANIFEST-v1.json';assert not out.exists()
    ready=R.HERE.parent/'READY-MANIFEST-v1.json';rd=json.loads(ready.read_text())
    prior=[check_manifest(ready,'36f837b4f15316b8501dec2f4e9c877dc2929739e9cd0a0b6aa5e48eae4cdea3','files')]
    for x in rd['prior_preservation']:prior.append(check_manifest(R.ROOT/x['manifest'],x['sha256'],'files'))
    author=[]
    for arm,(rel,pin) in R.PACKAGES.items():author.append(check_manifest(R.ROOT/'research/rmaf/algorithm/universal233'/rel,pin,'immutable_files'))
    # Reuse the actual production body/pin checker, not a parallel weak check.
    import audit as A
    for arm,version in [('maf','v1'),('groups','v2')]:
        d=json.loads((R.ROOT/f'research/rmaf/results/algorithm-maf-grouped-fresh-review-{arm}-rebuild-{version}.json').read_text())
        assert all(A.source_valid(x) for x in d['sources'])
    receipts=sorted((R.ROOT/'research/rmaf/results').glob('algorithm-maf-grouped-fresh-review-*.json'))
    final_audit=json.loads((R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-audit-v2.json').read_text())
    for x in final_audit['packages']:
        assert not x['audit']['forbidden'] and x['audit']['axiom_union']==['Classical.choice','Quot.sound','propext']
        for f in ('audit_build','dual_build','literal_print_build'):
            r=x[f];assert r['exit']==0 and R.sha(R.ROOT/r['log'])==r['log_sha256']
    maf=json.loads((R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-maf-readout-v1.json').read_text());assert maf['comparisons']==267 and all(x['pass'] for x in maf['checks']) and not maf['expectations_changed']
    grouped=json.loads((R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-groups-readout-v1.json').read_text());assert grouped['comparisons']==98 and grouped['status']=='FAIL_RETAINED_STRICT_FROZEN_GROUP_CROSS_EXPECTATION'
    qualification=json.loads((R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-groups-reference-qualification-v1.json').read_text());assert qualification['no_frozen_expectation_changed'] and not qualification['all_universal_reverse_premises_satisfied']
    child=json.loads((R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-child-readout-v1.json').read_text());assert child['partitions']==15 and len(child['contract_rows'])==3
    false=json.loads((R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-false-controls-v1.json').read_text());assert false['own_false_propositions']==20 and false['author_false_propositions']==7
    preservation={'status':'ALL_RELEASED_AND_PRIOR_FROZEN_FILES_MATCH','author':author,'prior':prior,'utc':datetime.now(timezone.utc).isoformat()};(R.HERE/'FINAL-PRESERVATION-v1.json').write_text(json.dumps(preservation,indent=2)+'\n')
    sources=sorted([p for p in R.HERE.rglob('*') if p.is_file()]+receipts)
    assert len(sources)==len(set(sources))
    rows=[{'path':str(p.relative_to(R.ROOT)),'realpath':str(p.resolve()),'sha256':R.sha(p),'bytes':p.stat().st_size} for p in sources]
    d={'version':1,'stage':'RELEASED_SCOPED_REVIEW_COMPLETE','utc':datetime.now(timezone.utc).isoformat(),'status':'COMPLETE_WITH_RETAINED_REFERENCE_AND_HARNESS_QUALIFICATIONS','immutable':True,'author_packages':author,'prior_preservation':prior,'all_main_milestones':{'Algorithm':'OPEN','Correctness':'OPEN','Smallerbase':'OPEN'},'replication_count_added':0,'same_graph_checker_lineage':True,'author_contacts':0,'children':0,'barred_live_source_contact':False,'copied_scientific_oleans':False,'separate_scoped_verdicts':{'original':'PASS_SCOPED_CONDITIONAL_ORIGINAL_DISJOINT_CALLER','grouped':'QUALIFIED_SCOPED_GROUPED_RECONSTRUCTION_RESULT'},'actual_readout':{'original_matching':267,'grouped_matching':98,'grouped_retained_reference_failures':1,'frozen_expected_values_changed':False,'child_partitions':15,'child_budget_rows':3},'final_positive_audits':[{'arm':x['arm'],'modules':len(x['positive_modules']),'origins':x['audit']['total'],'literal_theorems_printed':x['literal_theorems_printed'],'axiom_union':x['audit']['axiom_union']} for x in final_audit['packages']],'strict_false_propositions':{'own':20,'author':7},'qualifications':['One unchanged off-Owns frozen CrossClear reference expectation fails; no all-frozen-pass claim','One checked source-only lazy equation origin adoption, identical raw type/proof','Two child readout harness failures retained before successful literal control replay','First unfrozen own audit-v1 timing JSON bytes overwritten/lost; exact v2 bytes archived and original v1 log hashes reproduced','All prior weak/superseded control and author amendment histories preserved'],'supplied_open_imports':['Original callback attained-minimum soundness/completeness IH on actual restricted Q inputs','Grouped exact child-specific ResidualSolverContract at localTarget T B, current bs, q-1'],'not_certified':['Full recursive solver or well-founded dispatcher','Global optimum/rule coverage','Final original cut recovery','Machine semantics and full solver runtime','Smaller base or novelty'],'receipts':[{'path':str(p.relative_to(R.ROOT)),'sha256':R.sha(p)} for p in receipts],'files':rows,'file_count':len(rows),'total_bytes':sum(x['bytes'] for x in rows)}
    out.write_text(json.dumps(d,indent=2)+'\n');seal={'manifest':str(out.relative_to(R.ROOT)),'sha256':R.sha(out),'files':len(rows),'total_bytes':d['total_bytes']};(R.HERE/'REVIEW-SEAL-v1.json').write_text(json.dumps(seal,indent=2)+'\n')
    for p in sources+[out,R.HERE/'REVIEW-SEAL-v1.json']:p.chmod(p.stat().st_mode&~0o222)
    assert all(R.sha(R.ROOT/x['path'])==x['sha256'] for x in rows)
    print(json.dumps(seal))
if __name__=='__main__':main()
