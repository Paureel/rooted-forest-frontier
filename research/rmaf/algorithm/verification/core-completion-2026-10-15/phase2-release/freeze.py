"""Bind this completed scoped review; never mutate earlier frozen packages."""
from pathlib import Path
import hashlib,json,datetime,os
from rebuild import ROOT,HERE,digest

def main():
    checks=[]
    for path,key,expected in [
      ('research/rmaf/algorithm/universal233/source_coverage/SOURCE-COVERAGE-MANIFEST-v1.json','immutable_files','a153e4e878c2cde3bea73f604a01a4955ca1b8fd94e8baa1bc02833934f32e33'),
      ('research/rmaf/algorithm/universal233/cut_realization/CUT-REALIZATION-MANIFEST-v1.json','owned_files','61658da7b8868079dc471b82965da66e095beafbde509a726c5b930bed84a182'),
      ('research/rmaf/algorithm/verification/core-completion-2026-10-15/READINESS-MANIFEST-v2.json','immutable_snapshot_files','03c850d43d84457f4245a233f5c03a87396e90d545e91231ef56c928e3fdb59f')]:
        p=ROOT/path;assert digest(p)==expected;d=json.loads(p.read_text());items=d[key]
        if isinstance(items,dict):items=[{'path':k,'sha256':v} for k,v in items.items()]
        rows=[]
        for r in items:
            name=r.get('path',r.get('snapshot'));actual=digest(ROOT/name)
            assert actual==r['sha256'],name
            rows.append({'path':name,'sha256':actual})
        checks.append({'manifest':path,'sha256':expected,'files':len(rows),'all_match':True,'rows':rows})
    versions={}
    for short in ['source-rebuild-v1','cut-rebuild-v1','joint-v1','actual-readout-v1',
                  'graph-controls-v1','rejections-v2','origin-collision-v1',
                  'inventory-controls-v1','final-audit-v1']:
        p=ROOT/f'research/rmaf/results/algorithm-core-completion-fresh-review-{short}.json'
        d=json.loads(p.read_text());versions[short]={'path':str(p.relative_to(ROOT)),'sha256':digest(p)}
        if 'status' in d:assert d['status'].startswith('PASS'),(short,d['status'])
    report={'status':'PASS_NONAUTHOR_SOURCE_CORE_REVIEW','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'scope':'ordinary source generator only: actual original residual components/nonempty leaves/exact cuts; finite-budget F-refines-Q; all-output cut lower/upper; raw rational LIST mass for c>=2',
      'source_packages_unchanged':checks,'receipts':versions,
      'full_origin_counts':{'source':1604,'cut':1735,'joint_with_nonauthor_consumer':1945},
      'joint_modules':38,'literal_print_axioms_theorems':1154,
      'actual_program_fixtures':12,'literal_original_graph_assertions':118,
      'explicit_false_propositions_final':7,'historical_reduction_stuck_mass_attempts_not_counted':2,
      'algorithm':'OPEN','correctness':'OPEN','smaller_base':'OPEN',
      'full_solver_state_scaffold_certified':False,'polynomial_prefix_work_certified':False,
      'replication_count_added':0,'new_novelty_acceptance':False,
      'prior_contacts':'CONTACT-ADDENDUM.md and unchanged precontact CONTACT-LEDGER.md',
      'verdict':str((HERE/'VERDICT.md').relative_to(ROOT)),
      'failed_attempts':str((HERE/'FAILURE-LEDGER.md').relative_to(ROOT))}
    final=ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-final-v1.json'
    final.write_text(json.dumps(report,indent=2)+'\n')
    files=sorted(p for p in HERE.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name not in ['REVIEW-MANIFEST-v1.json','REVIEW-MANIFEST-v1.sha256'])
    # Include this entire new phase, including historical wrong/inconclusive
    # controls and superseded receipts. Their status is explicit, not erased.
    results=sorted((ROOT/'research/rmaf/results').glob('algorithm-core-completion-fresh-review-*.json'))
    current=[p for p in results if 'prep-' not in p.name] # preparation already pinned by readiness
    files=sorted(set(files+current))
    entries=[{'path':str(p.relative_to(ROOT)),'realpath':str(p.resolve()),'sha256':digest(p),'bytes':p.stat().st_size} for p in files]
    manifest={'version':1,'stage':'FROZEN_NONAUTHOR_SCOPED_COMPLETION_REVIEW','immutable':True,
      'utc':report['utc'],'verdict':'PASS_SCOPED_SOURCE_CORE','final_receipt':str(final.relative_to(ROOT)),
      'all_main_milestones':'OPEN','replication_count_added':0,
      'author_manifests':[{k:v for k,v in c.items() if k!='rows'} for c in checks],
      'positive_source_scope':'isolated source/cut source lists and mapped 38-module joint inventory; planted custom axioms occur only in rejection controls',
      'author_sources_mutated':False,'readiness_snapshots_mutated':False,
      'corrected_rejection_receipt':versions['rejections-v2'],
      'historical_rejections_v1':'retained; two rational records are INCONCLUSIVE, superseded by v2; not final evidence',
      'files':entries,'file_count':len(entries),'byte_total':sum(e['bytes'] for e in entries)}
    p=HERE/'REVIEW-MANIFEST-v1.json';p.write_text(json.dumps(manifest,indent=2)+'\n')
    sha=digest(p);q=HERE/'REVIEW-MANIFEST-v1.sha256';q.write_text(sha+'  REVIEW-MANIFEST-v1.json\n')
    for e in entries:assert digest(ROOT/e['path'])==e['sha256']
    for f in files+[p,q]:f.chmod(0o444)
    print('FROZEN',len(entries),'files',manifest['byte_total'],'bytes')
    print('SHA256',sha)

if __name__=='__main__':main()
