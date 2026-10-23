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
 # Full-path old truth/forged-closure controls execute before new module evidence.
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
 # Switch only the in-memory evidence location; original code/files remain frozen.
 check_semantics.HERE=HERE
 rr=check_semantics.receipt('geometry-own-body-v2')
 plan=json.loads((OLD/'COLD-SOURCE-PLAN-v1.json').read_text());mods=json.loads((HERE/'EVIDENCE-RUN-CONFIG-v2.json').read_text())['modules'];allowed=set(plan['order'])|set(mods)|{'ReconstructionV2','ControlFlowV4','CommonCoreV2','CommonRuleV2','ExpansionPartitionV2'}
 # New inductive/recursor corruption twins must fail before evidence acceptance.
 for mutation in ['missing-recursor-rhs','forged-recursor-ref','missing-inductive-payload','missing-constructor-extra','syntax-metadata']:
  bad=copy.deepcopy(rr)
  if mutation in ['missing-recursor-rhs','forged-recursor-ref']:
   r=next(r for r in bad if r.get('kind')=='recursor');rule=r['data_payload']['rules'][0]
   if mutation=='missing-recursor-rhs':rule.pop('rhs')
   else:rule['rhs']=['const','Forged.recursor',[]]
  elif mutation=='missing-inductive-payload':next(r for r in bad if r.get('kind')=='inductive')['data_payload'].pop('ctors')
  elif mutation=='missing-constructor-extra':next(r for r in bad if r.get('kind')=='constructor')['extra_refs']=[]
  else:
   r=next(r for r in bad if r.get('kind')=='definition');r['body']=['metadata',[[['anonymous'],['syntax-unencoded','unsupported retained control']]],r['body']]
  try:own_rows(bad,allowed)
  except (AssertionError,ValueError,TypeError,KeyError):catches.append(mutation)
  else:raise AssertionError('full row reader accepted corruption '+mutation)
 ds,bodyinfo=own_rows(rr,allowed);source_gate(ds)
 cr=check_semantics.receipt('geometry-own-closure-v2');deps,reach=check_closure.graph(cr)
 forbidden={'OrdinaryDispatch.FastOrdinary.solve_exact','OrdinaryDispatch.FastOrdinary.external_exact','OrdinaryDispatch.FastOrdinary.actual_ordinary_IH','OrdinaryDispatch.FastOrdinary.actual_local_ordinary_IH','Universal233.DepthOne.found_globally_minimum','OrdinaryDispatch.FastOrdinary.found_query_exact','OrdinaryDispatch.FastOrdinary.query_of_checked_complete'}

 forbidden.update({"OrdinaryDispatch.FastOrdinary.common_pair_ready","OrdinaryDispatch.FastOrdinary.common_pair_exact","OrdinaryDispatch.selected_common_ready","OrdinaryDispatch.selected_common_query_exact","OrdinaryDispatch.common_reduced_proper","OrdinaryDispatch.selected_common_label_decrease","OrdinaryDispatch.common_query_equivalence","OrdinaryDispatch.common_expansion_original","ForestState.contraction_proper","ForestState.common_cherry_contract_agreement","ForestState.common_cherry_expand_agreement","ForestState.common_cherry_decision_equivalence","ForestState.common_cherry_state_strict_decrease"})
 assert not (forbidden&set(deps))
 assert 'sorryAx' not in deps and not any(r['partial'] or r['unsafe'] for r in deps.values())
 roots={}
 for root in cr[0]['roots']:
  names=reach(root)
  auth=[n for n in sorted(names) if deps[n]['kind']=='theorem' and deps[n]['module'] in plan['order']]
  roots[root]={'declarations':len(names),'axioms':sorted(n for n in names if deps[n]['kind']=='axiom'),'author_theorem_dependencies':auth,'author_global_targets':sorted(names&forbidden)}
 runtime=[]
 for m in sorted({r['module'] for r in deps.values()}-allowed):
  p=RUNTIME/'lib/lean'/pathlib.Path(*m.split('.')).with_suffix('.olean');assert p.is_file()
  runtime.append({'module':m,**pin(p)})
 compiler=pin(RUNTIME/'bin/lean')
 previous=json.loads((HERE.parent/'resume_20261016T083330Z/FINAL-MANIFEST-v1.json').read_text())
 previouspins={r['path']:r for r in previous['files']}
 tools=[]
 for name in ['instrument-v5/Producer.lean','instrument-v5/Producer.olean','instrument-v5/AxiomClosure.lean','instrument-v6/Producer.lean','instrument-v6/Producer.olean','instrument-v6/StoredInvoke.lean']:
  p=OLD/name;cur=pin(p);assert cur==previouspins[str(p.resolve())];tools.append(cur)
 result={'status':'NEW-QUANTIFIED-PROOF-BODY-AND-ACTUAL-CLOSURE-CHECKED','body':bodyinfo,'roots':roots,'closure_declarations':len(deps),'axioms':cr[-1]['axioms'],'forbidden_targets_checked':sorted(forbidden),'forbidden_reached':[],'custom_axioms':sorted(n for n,r in deps.items() if r['kind']=='axiom' and r['module'] in allowed),'sorryAx':False,'partial':[],'unsafe':[],'controls_caught':catches,'cached_axiom_extension_used':False,'new_source':pin(HERE/'ActualCommonLiftV2.lean'),'new_olean':pin(HERE/'ActualCommonLiftV2.olean'),'compiler':compiler,'trusted_runtime_pins':runtime,'unchanged_calibrated_producer_pins':tools,'independent_full_solver_exactness':False,'rejected_arm_open':True,'new_blind_credit':False}
 result["new_module_pins"]=[pin(HERE/(m+ext)) for m in mods for ext in [".lean",".olean"]]
 result["common_ready_proved_with_explicit_primitive_reuse"]=True
 result["common_lift_geometric_premises_open"]=False
 result["expansion_geometry_proved"]=True
 result["coarsening_geometry_proved"]=True
 result["common_lift_proved_with_explicit_primitive_reuse"]=True
 result["remaining_conditional_parameters"]=["OneRule","HighRule","ForwardRule4","ReverseRule4","Hard2Rule","RejectImpossible"]
 write('GEOMETRY-DEPENDENCY-CERTIFICATE-v1.json',result)
 print(json.dumps({'status':result['status'],'body':bodyinfo,'closure_declarations':len(deps),'axioms':result['axioms'],'forbidden_reached':[],'per_root_author_theorem_counts':{n:len(r['author_theorem_dependencies']) for n,r in roots.items()},'runtime_modules':len(runtime)},sort_keys=True))
if __name__=='__main__':main()
