"""Own calibrated full stored-row consumer, with explicit pinned author/own module boundary.
The only row-parser adaptation is allowed-module resolution for the current entry chain.
No raw-author audit or oracle execution. Full recursor RHS and metadata checks retained.
"""
import copy,gzip,hashlib,json,pathlib,sys
HERE=pathlib.Path(__file__).resolve().parent;OLD=HERE.parent/'postrelease-v1'
sys.path.insert(0,str(OLD))
import check_closure,check_semantics
from row_audit_metadata import expression,source_gate,rowhash
from scan_rows import read_label
RUNTIME=HERE.parents[6]/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0'
def pin(p):
 p=pathlib.Path(p);return {'path':str(p.resolve()),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def write(n,v):
 with (HERE/n).open('x') as f:json.dump(v,f,indent=2,sort_keys=True);f.write('\n')

def own_rows(rr,allowed,expected=None):
    header=rr[0];decls=[r for r in rr[1:] if 'record' not in r]
    external=[r for r in rr[1:] if r.get('record')=='external-trust-boundary']
    if len(decls)!=header['count'] or not decls:raise ValueError('missing/zero rows')
    if any(r.get('record') not in (None,'external-trust-boundary') for r in rr[1:]):raise ValueError('unknown row')
    names=[r['name'] for r in decls]
    if len(names)!=len(set(names)):raise ValueError('duplicate declaration rows')
    externals={r['name']:r for r in external}
    if len(externals)!=len(external):raise ValueError('duplicate external rows')
    if header['import_level']!='private':raise ValueError('private imports required')
    all_refs=set();walked=0;proofs=0;recursor_rules=0
    for r in decls:
        if r['module'] not in header['modules']:raise ValueError('module provenance')
        tr,tn=expression(r['type']);walked+=tn
        if tr!=set(r['type_refs']):raise ValueError('type dependency mismatch')
        k=r['kind'];body=r['body'];payload=r['data_payload'];extra=set()
        fields={
            'definition':{'safety','hints','all'},'theorem':{'all'},'opaque':{'all'},'axiom':set(),
            'inductive':{'all','ctors','numParams','numIndices','numNested','isRec','isReflexive'},
            'constructor':{'induct','cidx','numParams','numFields'},
            'recursor':{'all','numParams','numIndices','numMotives','numMinors','k','rules'},
            'quotient':{'quotKind'}}
        if k not in fields or set(payload)!=fields[k]:raise ValueError('incomplete nonproof data payload')
        if k in ('definition','opaque'):
            if body is None or r['proof_body_omitted_after_actual_walk']:raise ValueError('nonproof body missing')
            br,bn=expression(body);walked+=bn
            if br!=set(r['body_refs']) or bn!=r['body_nodes']:raise ValueError('body walk mismatch')
        elif k=='theorem':
            if body is not None or not r['proof_body_omitted_after_actual_walk'] or r['body_nodes']<1:
                raise ValueError('proof body actual-walk attestation')
            proofs+=1
        elif body is not None or r['body_nodes']!=0 or r['body_refs']:
            raise ValueError('unexpected body')
        if k=='inductive':extra.update(payload['all']);extra.update(payload['ctors'])
        elif k=='constructor':extra.add(payload['induct'])
        elif k=='recursor':
            extra.update(payload['all'])
            for rule in payload['rules']:
                if set(rule)!={'ctor','nfields','rhs'}:raise ValueError('recursor rule payload')
                rr0,nn=expression(rule['rhs']);extra.update(rr0);extra.add(rule['ctor']);walked+=nn;recursor_rules+=1
        if extra!=set(r['extra_refs']):raise ValueError('extra dependency mismatch')
        all_refs.update(tr);all_refs.update(r['body_refs']);all_refs.update(extra)
    if all_refs-set(names)-set(externals):raise ValueError('unknown declaration reference')
    if set(externals)-all_refs:raise ValueError('extraneous trust boundary')
    for name,r in externals.items():
        if r['module'] in allowed:continue
        # Name prefixes alone are insufficient. Resolve every recorded trusted
        # module to the pinned installed runtime, with no project lookup.
        if not r['module'].startswith(('Init.','Lean.','Std.')) and r['module'] not in ('Init','Lean','Std'):
            raise ValueError('unlicensed external module')
        p=RUNTIME/'lib/lean'/pathlib.Path(*r['module'].split('.')).with_suffix('.olean')
        if not p.is_file() or not p.resolve().is_relative_to(RUNTIME.resolve()):raise ValueError('external binary path')
    if expected is not None:
        actual={r['name']:rowhash(r) for r in decls}
        if actual!=expected:raise ValueError('missing/altered row commitment')
    source_gate({r['name']:r for r in decls})
    return {r['name']:r for r in decls},{'rows':len(decls),'full_expression_nodes_walked':walked,
        'proofs_actual_walk_attested':proofs,'recursor_rules_walked':recursor_rules,'trusted_external_names':len(externals)}

def main():
 check_closure.controls()
 clean=read_label('fixed-clean');own_rows(clean,{'PClean'})
 catches=[]
 for mutation in ['missing-row','duplicate-row','missing-nonproof-body','forged-reference','partial']:
  bad=copy.deepcopy(clean);i=next(i for i,r in enumerate(bad) if r.get('kind')=='definition')
  if mutation=='missing-row':bad.pop(i)
  elif mutation=='duplicate-row':bad.append(copy.deepcopy(bad[i]))
  elif mutation=='missing-nonproof-body':bad[i]['body']=None
  elif mutation=='forged-reference':bad[i]['body_refs'].append('Forged.missing')
  else:bad[i]['partial']=True
  try:own_rows(bad,{'PClean'})
  except (AssertionError,ValueError,TypeError):catches.append(mutation)
  else:raise AssertionError('new module reader accepted corruption '+mutation)
 check_semantics.HERE=HERE
 rr=check_semantics.receipt('exchange-own-body-v2')
 plan=json.loads((OLD/'COLD-SOURCE-PLAN-v1.json').read_text())
 config=json.loads((HERE/'EVIDENCE-RUN-CONFIG-v2.json').read_text());mods=config['modules']
 geom=json.loads((HERE.parent/'common_geometry_20261016T094138Z/EVIDENCE-RUN-CONFIG-v5.json').read_text())['modules']
 paid=json.loads((HERE.parent/'paid_rule_reconstruction_20261016T101119Z/EVIDENCE-RUN-CONFIG-v2.json').read_text())['modules']
 allowed=set(plan['order'])|set(mods)|set(geom)|set(paid)|{'ReconstructionV2','ControlFlowV4','CommonCoreV2','CommonRuleV2','ExpansionPartitionV2'}
 bad=copy.deepcopy(rr);r=next(r for r in bad if r.get('kind')=='definition')
 r['body']=['metadata',[[['anonymous'],['syntax-unencoded','unsupported retained control']]],r['body']]
 try:own_rows(bad,allowed)
 except (AssertionError,ValueError,TypeError,KeyError):catches.append('syntax-metadata')
 else:raise AssertionError('full row reader accepted Syntax metadata')
 ds,bodyinfo=own_rows(rr,allowed)
 cr=check_semantics.receipt('exchange-own-closure-v2');deps,reach=check_closure.graph(cr)
 assert cr[0]['roots']==config['roots']
 forbidden={
  'OrdinaryDispatch.FastOrdinary.solve_exact','OrdinaryDispatch.FastOrdinary.external_exact',
  'OrdinaryDispatch.FastOrdinary.actual_ordinary_IH','OrdinaryDispatch.FastOrdinary.actual_local_ordinary_IH',
  'Universal233.DepthOne.found_globally_minimum','OrdinaryDispatch.FastOrdinary.found_query_exact',
  'OrdinaryDispatch.FastOrdinary.query_of_checked_complete','OrdinaryDispatch.forest_child_exact_at',
  'GenericForest.LocalIH.exact_at_budget_bound','GenericForest.exact_of_ordinary',
  'Universal233.CherryBranching.ordinary_branches_cover','Universal233.CherryBranching.high_branches_cover',
  'Universal233.CherryBranching.actual_t1_pendant_exchange','Universal233.CherryBranching.actual_pendant_safety',
  'Universal233.CherryBranching.actual_high_safety','Universal233.CherryBranching.refined_length',
  'Universal233.CherryBranching.paid_budget_identity','Universal233.CherryBranching.branch_checks',
  'OrdinaryDispatch.one_child_complete','OrdinaryDispatch.runChildren_complete','OrdinaryDispatch.three_children_complete',
  'OrdinaryDispatch.query_complete','OrdinaryDispatch.runChildren_minimum',
  'RestrictionBridge.root_not_prepend','RestrictionBridge.root_not_prepend._simp_1',
  'ForestState.common_cherry_contract_agreement','ForestState.common_cherry_expand_agreement',
  'ForestState.common_cherry_decision_equivalence','OrdinaryDispatch.common_expansion_original',
  'OrdinaryDispatch.selected_common_query_exact','OrdinaryDispatch.common_query_equivalence'}
 assert not forbidden&set(deps)
 for name in deps:
  assert not name.startswith(('Universal233.CherryBranching.actual_t1_', 'OrdinaryDispatch.FastOrdinary.actual_ordinary_')),name
 assert 'sorryAx' not in deps
 assert not any(r['partial'] or r['unsafe'] for r in deps.values())
 generated={
 'RMAF.leaves.eq_1','RMAF.leaves.eq_2','RMAF.pairwiseEmbeddings.eq_2',
 'Universal233.Rule4.instDecidableLocalGuard._proof_1','Universal233.Rule4.instDecidableLocalGuard._proof_2',
 'Universal233.Rule4.instDecidablePriority._proof_1'}
 author={n for n,r in deps.items() if r['kind']=='theorem' and r['module'] in plan['order']}
 assert author==generated,sorted(author-generated)
 roots={}
 for root in config['roots']:
  names=reach(root);auth=sorted(n for n in names if n in author)
  roots[root]={'declarations':len(names),'axioms':sorted(n for n in names if deps[n]['kind']=='axiom'),
   'author_theorem_dependencies_reused':auth,'author_global_targets':sorted(names&forbidden),
   'open_Prop_definition_only':root in config['roots'][-3:]}
 core=['crossing_boundary_in_minimal','one_crossing_block','split_one_bound','original_split_count','original_split_label_count']
 assert all(not roots['IndependentOneExchange.'+r]['author_theorem_dependencies_reused'] for r in core)
 runtime=[]
 for m in sorted({r['module'] for r in deps.values()}-allowed):
  assert m in ('Init','Lean','Std') or m.startswith(('Init.','Lean.','Std.'))
  p=RUNTIME/'lib/lean'/pathlib.Path(*m.split('.')).with_suffix('.olean');assert p.is_file()
  runtime.append({'module':m,**pin(p)})
 previous=json.loads((HERE.parent/'resume_20261016T083330Z/FINAL-MANIFEST-v1.json').read_text())
 previouspins={r['path']:r for r in previous['files']};tools=[]
 for name in ['instrument-v5/Producer.lean','instrument-v5/Producer.olean','instrument-v5/AxiomClosure.lean','instrument-v6/Producer.lean','instrument-v6/Producer.olean','instrument-v6/StoredInvoke.lean']:
  p=OLD/name;cur=pin(p);assert cur==previouspins[str(p.resolve())];tools.append(cur)
 pins=[pin(HERE/(m+e)) for m in mods for e in ['.lean','.olean']]
 assert pins==json.loads((HERE/'PRE-AUDIT-SOURCE-OLEAN-LOCK-v2.json').read_text())['files']
 negatives=[]
 for label in ['negative-selected-refinement-v2','negative-falsesingletondrop-v1','negative-falseboundarycount-v1']:
  receipts=[json.loads(p.read_text()) for p in (HERE/'evidence').glob('*.json') if json.loads(p.read_text()).get('label')==label]
  assert len(receipts)==1
  receipt=receipts[0];assert receipt['returncode']==1 and receipt['stop_reason'] is None
  raw=''
  for shard in receipt['shards']:
   p=HERE/shard['path'];assert pin(p)['sha256']==shard['sha256']
   with gzip.open(p,'rt') as f:raw+=f.read()
  assert 'Tactic `decide` proved that the proposition' in raw and 'is false' in raw
  negatives.append(label)
 result={'status':'SUBSTANTIVE-PARTIAL-ONE-EXCHANGE-OPEN',
  'body':bodyinfo,'body_kind_counts':{k:sum(r['kind']==k for r in ds.values()) for k in sorted({r['kind'] for r in ds.values()})},
  'roots':roots,'closure_declarations':len(deps),'axioms':cr[-1]['axioms'],
  'forbidden_targets_checked':sorted(forbidden),'forbidden_reached':[],
  'custom_axioms':sorted(n for n,r in deps.items() if r['kind']=='axiom' and r['module'] in allowed),
  'sorryAx':False,'partial':[],'unsafe':[],'controls_caught':catches,
  'explicit_false_proposition_controls':negatives,'initial_namespace_failure_preserved_not_counted':True,
  'cached_axiom_extension_used':False,'new_module_pins':pins,'compiler':pin(RUNTIME/'bin/lean'),
  'trusted_runtime_pins':runtime,'unchanged_calibrated_producer_pins':tools,
  'author_theorem_dependency_allowlist_exact':sorted(generated),
  'new_author_mathematical_primitives':[],'first_open_step':'IndependentOneExchange.OriginalCladeSplitAgreement',
  'endpoint_reattachment_open':'IndependentOneExchange.SinglePendantRepair',
  'actual_selected_exchange_open':'IndependentOneExchange.SelectedOnePendantExchange',
  'one_pendant_exchange_open':True,'residual_forest_transfer_open':True,'cherry_forest_dichotomy_open':True,
  'six_original_rule_parameters_remain_open':['OneRule','HighRule','ForwardRule4','ReverseRule4','Hard2Rule','RejectImpossible'],
  'source_read_scope_breach':True,'incident':pin(HERE/'SOURCE-READ-INCIDENT-v1.json'),
  'no_new_independent_high_coverage_claim':True,'no_forbidden_target_application_accepted':True,
  'new_blind_credit':0,'new_replication_credit':0,'independent_full_solver_exactness':False,
  'runtime_equivalence_proved':False,'raw_global_cleanliness_claimed':False}
 assert set(result['axioms'])=={'propext','Classical.choice','Quot.sound'} and not result['custom_axioms']
 write('ONE-EXCHANGE-DEPENDENCY-CERTIFICATE-v1.json',result)
 write('NEW-DECLARATION-COMMITMENTS-v1.json',{'rows':{n:rowhash(r) for n,r in sorted(ds.items())},'actual_stored_body_walk':True,'source_olean_lock':pin(HERE/'PRE-AUDIT-SOURCE-OLEAN-LOCK-v2.json')})
 print(json.dumps({'status':result['status'],'body':bodyinfo,'kind_counts':result['body_kind_counts'],'closure_declarations':len(deps),'axioms':result['axioms'],'forbidden_reached':[],'per_root_author_theorem_counts':{n:len(r['author_theorem_dependencies_reused']) for n,r in roots.items()},'runtime_modules':len(runtime)},sort_keys=True))
if __name__=='__main__':main()
