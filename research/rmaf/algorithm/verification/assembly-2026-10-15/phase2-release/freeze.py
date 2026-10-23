"""Final source-bound review freeze; old author/READY/core files stay intact."""
from pathlib import Path
import json,datetime
from rebuild import ROOT,HERE,digest

def main():
    records=[]
    base=ROOT/'research/rmaf/algorithm/universal233'
    for rel,expected in [
      ('assembly/ASSEMBLY-MANIFEST-v1.json','c7fd11453b315ad94b13fc8f440837ebd4ac3e0f92697275dbfd3d90879949bf'),
      ('whole_source_mass/WHOLE-SOURCE-MASS-MANIFEST-v1.json','b422a7fa142bf06669cc7abdce581a7e791a672494ec2db159ce5aad9e0d5fb0'),
      ('assembly_completion/ASSEMBLY-COMPLETION-MANIFEST-v1.json','6efd06c43f8d84538ab6a215329b4b30f62ed2cb039632c6dfe70009faf1d6cd')]:
        p=base/rel;assert digest(p)==expected;d=json.loads(p.read_text())
        for r in d['immutable_files']:assert digest(ROOT/r['path'])==r['sha256'],r['path']
        records.append({'manifest':str(p.relative_to(ROOT)),'sha256':expected,'files':len(d['immutable_files']),'all_match':True})
    p=base/'hard_parent_refinement/HARD-PARENT-REFINEMENT-MANIFEST-v1.json'
    assert digest(p)=='e8177aebdebc839587763ef731785002a8a08b5608530aabc6336177557cd337';d=json.loads(p.read_text())
    for path,h in d['exact_source_import_pins'].items():assert digest(ROOT/path)==h,path
    receipt=ROOT/d['receipt']/'RECEIPT-FILES.json';assert digest(receipt)==d['receipt_files_hash']
    members=json.loads(receipt.read_text())
    for name,r in members.items():assert digest(receipt.parent/name)==r['sha256'],name
    records.append({'manifest':str(p.relative_to(ROOT)),'sha256':digest(p),'source_pins':len(d['exact_source_import_pins']),
      'receipt_files':len(members),'receipt_list_sha256':digest(receipt),'all_match':True})
    for path,sha,n in [
      ('research/rmaf/algorithm/verification/assembly-2026-10-15/READY-MANIFEST-v1.json','43dae592987367d46b84f5254687928c5cd327bb1edb6aaef765d9b5a4f29c5b',45),
      ('research/rmaf/algorithm/verification/core-completion-2026-10-15/phase2-release/REVIEW-MANIFEST-v1.json','c4c316fcd484d51cc1cebafbf69a9fa9b7500e56cc93b4617fb33326c69af7db',377)]:
        p=ROOT/path;assert digest(p)==sha;d=json.loads(p.read_text());assert d['file_count']==n
        for r in d['files']:assert digest(ROOT/r['path'])==r['sha256'],r['path']
        records.append({'manifest':path,'sha256':sha,'files':n,'all_unchanged':True})
    results=sorted((ROOT/'research/rmaf/results').glob('algorithm-assembly-fresh-review-*.json'))
    receipts=[]
    for p in results:
        d=json.loads(p.read_text())
        if isinstance(d,dict) and 'status' in d:assert d['status'].startswith('PASS'),(p,d['status'])
        receipts.append({'path':str(p.relative_to(ROOT)),'sha256':digest(p)})
    summary={'status':'PASS_NONAUTHOR_SCOPED_ASSEMBLY_CONSUMER','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'scope':['generated original source-valid partition/embeddings','actual original hard2 singleton/refinement safety',
        'three actual whole-source F-to-Q-to-P forest covers','same literal color/output lists and rational raw multiplicity mass'],
      'manifest_checks':records,'source_module_origin_counts':{'assembly':2117,'mass':1738,'hard':1630,'completion':2491},
      'completion_with_nonauthor_consumer_origins':2563,'literal_axiom_print_theorems':1614,
      'positive_false_control_origins_separately_audited':52,
      'actual_readout_comparisons':123,'full_frozen_positive_comparisons':207,'full_frozen_false_catches':52,
      'addendum_positive_groups':3,'addendum_false_catches':9,'actual_output_replay_uses':41,
      'explicit_false_propositions_rejected':15,'inconclusive_diagnostics_counted':0,
      'numeric_joint_encoding_adapter':'none: exact base4 match',
      'reference_order_adapter':'four-chain BC/BB/AC/AB versus AB/AC/BB/BC; universal multiplicity-preserving Perm proof',
      'algorithm':'OPEN','correctness':'OPEN','smaller_base':'OPEN','replication_count_added':0,
      'full_recursive_solver_certified':False,'target_agreement_of_Q_certified':False,
      'remaining_budget_state_accounting_certified':False,'termination_runtime_global_base_certified':False,
      'excluded_live_sources_contacted':False,'authors_messaged':False,
      'verdict':str((HERE/'VERDICT.md').relative_to(ROOT)),
      'failures':str((HERE/'FAILURE-LEDGER.md').relative_to(ROOT)),'receipts':receipts}
    final=ROOT/'research/rmaf/results/algorithm-assembly-fresh-review-final-v1.json';final.write_text(json.dumps(summary,indent=2)+'\n')
    files=sorted(p for p in HERE.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name not in ['REVIEW-MANIFEST-v1.json','REVIEW-MANIFEST-v1.sha256'])
    files=sorted(set(files+results+[final]))
    rows=[{'path':str(p.relative_to(ROOT)),'realpath':str(p.resolve()),'sha256':digest(p),'bytes':p.stat().st_size} for p in files]
    manifest={'version':1,'stage':'FROZEN_NONAUTHOR_SCOPED_ASSEMBLY_REVIEW','immutable':True,
      'verdict':'PASS_SCOPED_ASSEMBLY_CONSUMER','utc':summary['utc'],'final_receipt':str(final.relative_to(ROOT)),
      'author_and_prior_freeze_checks':records,'all_main_milestones':'OPEN','replication_count_added':0,
      'positive_scope':'60 author modules plus NonauthorConsumer; clean false-control twin separately audited; planted axioms and intentional false controls excluded from positive imports',
      'files':rows,'file_count':len(rows),'bytes':sum(r['bytes'] for r in rows)}
    p=HERE/'REVIEW-MANIFEST-v1.json';p.write_text(json.dumps(manifest,indent=2)+'\n')
    sha=digest(p);q=HERE/'REVIEW-MANIFEST-v1.sha256';q.write_text(sha+'  REVIEW-MANIFEST-v1.json\n')
    for r in rows:assert digest(ROOT/r['path'])==r['sha256']
    for f in files+[p,q]:f.chmod(0o444)
    print('FROZEN',len(rows),'files',manifest['bytes'],'bytes')
    print('SHA256',sha)

if __name__=='__main__':main()
