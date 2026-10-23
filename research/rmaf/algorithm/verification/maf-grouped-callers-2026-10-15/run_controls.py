"""Frozen original disjoint-caller and grouped reconstruction plants."""
from pathlib import Path
from copy import deepcopy
from fractions import Fraction
from datetime import datetime,timezone
import hashlib,json,sys,time,traceback
sys.dont_write_bytecode=True
import instrument as I
HERE=Path(__file__).resolve().parent;ROOT=I.ROOT
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 mode=sys.argv[1];assert mode in ('pilot','full')
 freeze=json.loads((HERE/'CONTROL-FREEZE-v1.json').read_text())
 for r in freeze['files']:assert sha(ROOT/r['path'])==r['sha256'],r['path']
 E=json.loads((HERE/'EXPECTATIONS-v1.json').read_text());negplan=json.loads((HERE/'NEGATIVES-v1.json').read_text())
 dest=ROOT/f'research/rmaf/results/algorithm-maf-grouped-prerelease-{mode}-v1.json'
 start=time.monotonic();checks=[];negative=[];details=[]
 def check(name,v,e=True):
  checks.append({'id':name,'pass':v==e});assert v==e,(name,v,e)
 def catch(name,accepts):
  negative.append({'id':name,'caught':not bool(accepts)});assert not accepts,name
 result={'stage':'PRE_CANDIDATE_ONLY','mode':mode,'utc':datetime.now(timezone.utc).isoformat(),'candidate_contact':False,'candidate_compilation':False,'all_main_milestones':'OPEN','replication_count_added':0,'control_freeze_sha256':sha(HERE/'CONTROL-FREEZE-v1.json')}
 try:
  originals=[x for x in E['original_cases'] if mode=='full' or x['id'] in E['pilot_original_ids']]
  groups=[x for x in E['grouped_cases'] if mode=='full' or x['id'] in E['pilot_group_ids']]
  original_results={};group_results={}
  for c in originals:
   n=c['id'];check(n+'/original-guards',I.original_guard(c['source'],c['target'],c['Q']))
   r=I.run_caller(c);original_results[n]=r
   check(n+'/literal-call-occurrences',r['trace'],c['expected_calls'])
   for j,U in enumerate(c['Q']):
    s,t=I.restrict(c['source'],U),I.restrict(c['target'],U);minimum,ws=I.local_minimum(s,t)
    check(n+f'/slot{j}/exact-local-minimum',minimum,c['local_minima'][j])
    check(n+f'/slot{j}/local-witness',I.agreement(s,t,c['witnesses'][j]))
    if not c['out_of_minimum_contract']:check(n+f'/slot{j}/attained-witness',len(c['witnesses'][j])-1,minimum)
    stored=r['slots'][j]['stored'];check(n+f'/slot{j}/pretest-cost',None if stored is None else len(stored)-1,None if minimum>=2 else minimum)
   check(n+'/literal-concatenation',r['forest'],c['expected_forest'])
   if r['forest'] is not None:
    check(n+'/global-original-agreement',I.agreement(c['source'],c['target'],r['forest']))
    check(n+'/global-refines-Q',I.G.refines(r['forest'],c['Q']))
    check(n+'/additional-cost',r['additional'],c['expected_additional']);check(n+'/original-cut-cost',r['original_cuts'],c['expected_original_cuts'])
    check(n+'/sum-local-costs',r['additional'],sum(c['local_minima']))
   for base in (Fraction(2),Fraction(233,100)):
    m=I.normalized_mass(r['trace'],c['q'],base)
    if n in ('two-hard-q4','two-hard-q5','duplicate-slot-identities','reordered-Q'):check(n+f'/mass{base}',m,2/base**2);check(n+f'/two-genuine-bad-bound{base}',m<=1/base)
    if n=='stored-one-hard-two':check(n+f'/mass{base}',m,1/base)
    if n in ('sole-hard-no-discount','hard-plus-zero'):check(n+f'/mass{base}',m,Fraction(1))
   details.append({'id':n,'type':'original','actual':r})
  for c in groups:
   n=c['id'];r=I.grouped(c['target'],c['sources'],c['Q'],c['F']);group_results[n]=r
   for name,key in [('proper','proper'),('ownership','whole_source_ownership'),('cross','cross_piece_clear'),('global_agrees','global_agreement'),('additional','additional'),('whole_group_disjoint','whole_group_hulls_disjoint'),('within','within_group_overlap')]:check(n+'/'+name,r[name],c[key])
   check(n+'/literal-local-costs',[x['cost'] for x in r['local']],c['local_costs'])
   if r['global_agrees'] and r['ownership'] and r['checked_Q']:
    check(n+'/forward-local-validity',all(x['agrees'] for x in r['local']))
    check(n+'/all-safe-Nat-subtractions',r['integer_additional']>=0 and all(x['integer_cost']>=0 for x in r['local']))
    check(n+'/summed-additional-identity',sum(x['cost'] for x in r['local']),r['additional'])
    check(n+'/source-occurrences-preserved',sum(len(x['sources']) for x in r['local']),len(c['sources']))
    check(n+'/block-occurrences-preserved',I.G.canonical([b for x in r['local'] for b in x['forest']]),I.G.canonical(c['F']))
   if r['cross'] and r['ownership'] and r['proper'] and r['checked_Q'] and all(x['agrees'] for x in r['local']):check(n+'/reverse-concatenation',I.state_agrees(c['target'],c['sources'],[b for x in r['local'] for b in x['forest']]))
   details.append({'id':n,'type':'grouped','actual':r})
  # Comparator/trace twins, with no hidden finite-minimum access by runtime.
  first=E['original_cases'][0];r=I.run_caller(first);check('clean-twin/two-hard',r['trace'],first['expected_calls'])
  catch('total-versus-additional',r['original_cuts']==r['additional'])
  catch('initial-Q-charge-omitted',r['original_cuts']<=first['q'])
  catch('omit-call',r['trace'][:-1]==first['expected_calls'])
  catch('duplicate-call',r['trace']+[r['trace'][0]]==first['expected_calls'])
  forged=deepcopy(r['trace']);forged[0]['slot']=99;catch('unrelated-charged-trace',forged==first['expected_calls'])
  old=I.local_minimum
  def poison(*args):raise RuntimeError('unknown optimum read by runtime')
  I.local_minimum=poison
  try:check('clean-twin/no-minimum-oracle',I.run_caller(first)['trace'],first['expected_calls'])
  finally:I.local_minimum=old
  cheated=False
  try:poison(first)
  except RuntimeError:cheated=True
  catch('hidden-minimum-access',not cheated)
  if mode=='full':
   O={x['id']:x for x in E['original_cases']};GR={x['id']:x for x in E['grouped_cases']}
   dup=original_results['duplicate-slot-identities'];catch('deduplicate-slot-identities',dup['trace'][:1]==O['duplicate-slot-identities']['expected_calls'])
   failed=original_results['first-recursive-failure'];catch('charge-successes-only',failed['trace']==[])
   over=original_results['individually-ok-joint-over-budget'];catch('individually-successful-joint-budget',over['forest'] is not None)
   catch('forged-attained-minimum',len(O['individually-ok-joint-over-budget']['witnesses'][0])-1==O['individually-ok-joint-over-budget']['local_minima'][0])
   catch('missing-recursive-completeness',failed['forest'] is not None)
   catch('sole-hard-discount',I.normalized_mass(original_results['sole-hard-no-discount']['trace'],2,Fraction(2))<=Fraction(1,2))
   catch('q3-unpaid-recursive-call',original_results['two-hard-q3-reject']['trace']!=[])
   for c in E['malformed_original_cases']:
    check('malformed/'+c['id'],I.original_guard(c['source'],c['target'],c['Q']),c['valid'])
    if 'request' in c:
     check('malformed/'+c['id']+'/literal-suppression',I.restrict(c['source'],c['request']),c['restriction'])
    if 'source_embeddings' in c:
     check('malformed/'+c['id']+'/source-hulls',I.embeddings(c['source'],c['Q']),c['source_embeddings']);check('malformed/'+c['id']+'/target-hulls',I.embeddings(c['target'],c['Q']),c['target_embeddings'])
   m=E['malformed_original_cases'][0];catch('silent-absent-label-suppression',CounterSafe(I.leaves(I.restrict(m['source'],m['request'])))==CounterSafe(m['request']))
   m=next(x for x in E['malformed_original_cases'] if x['id']=='target-guard-only');catch('source-only-target-guard',I.agreement(m['source'],m['target'],m['Q']))
   m=next(x for x in E['malformed_original_cases'] if x['id']=='source-guard-only');catch('missing-source-embedding',I.original_guard(m['source'],m['target'],m['Q']))
   catch('forged-local-agreement',I.agreement(I.restrict(first['source'],first['Q'][0]),I.restrict(first['target'],first['Q'][0]),[first['Q'][0]]))
   catch('forged-global-agreement',I.agreement(first['source'],first['target'],first['Q']))
   root=GR['root-overlapping-B'];rr=group_results[root['id']]
   catch('drop-within-B-overlap',not rr['within'])
   catch('replace-piece-clear-by-group-hulls',group_results['whole-group-hulls-overlap-only']['whole_group_disjoint'])
   catch('infer-cross-clear-from-local-validity',group_results['cross-group-overlap-bad-concat']['cross'])
   catch('forbid-every-cross-overlap-output',not group_results['cross-group-overlap-refined-valid']['global_agrees'])
   catch('missing-whole-source-ownership',group_results['missing-whole-source-ownership']['ownership'])
   catch('wrong-source-component-subtraction',len(root['F'])-len(root['Q'])==rr['additional'])
   wholeF=[[0,1],[2],[3,4,5,6],[7]];catch('free-whole-parent-replacement',I.state_agrees(root['target'],root['sources'],wholeF))
   replaced=[root['sources'][0],[[3,4],[5,6]],root['sources'][-1]];check('clean-twin/replaced-problem-differs',I.state_agrees(root['target'],replaced,wholeF))
   catch('singleton-B-must-be-minimum',rr['local'][1]['cost']==group_results['root-cheaper-B-valid']['local'][1]['cost'])
   none=group_results['none-nonempty-source'];catch('unjustified-Nat-subtraction',none['integer_additional']==none['additional'])
   ce=GR['C-absent'];catch('empty-C-group-is-checked',I.partition(I.leaves(ce['target']),ce['Q']+[[]]))
   Echild=E['child'];contract={'target':Echild['target'],'sources':Echild['sources'],'kind':'ResidualFeasibility'}
   for row in Echild['queries']:
    child=I.child_query(Echild,row['q'],contract);check(f'child/q{row["q"]}/literal-budget',child['budget'],row['child_budget']);check(f'child/q{row["q"]}/success',child['forest'] is not None,row['success'])
    if row['success']:
     check(f'child/q{row["q"]}/literal-B-witness',child['forest'],row['B_forest']);check(f'child/q{row["q"]}/cost',len(child['forest'])-len(Echild['sources']),row['B_cost'])
     globalF=[[0,1],[2]]+child['forest']+[[7]];check(f'child/q{row["q"]}/global-agreement',I.state_agrees(root['target'],root['sources'],globalF));check(f'child/q{row["q"]}/actual-budget',len(globalF)-len(root['sources'])<=row['q'])
   catch('missing-residual-contract',I.child_query(Echild,3,None)['budget']==2)
   badcontract={**contract,'sources':[Echild['free_whole_parent']]};catch('wrong-child-specific-contract',I.child_query(Echild,3,badcontract)['budget']==2)
   catch('q0-underflow-child-execution',I.child_query(Echild,0,contract)['budget']==0)
   catch('forged-B-child-agreement',I.state_agrees(Echild['target'],Echild['sources'],Echild['invalid_whole_B_forest']))
   badF=deepcopy(root['F']);badF.append(deepcopy(root['F'][0]));catch('duplicate-global-block',I.state_agrees(root['target'],root['sources'],badF))
   catch('omit-owned-source-piece',sum(len(x['sources']) for x in rr['local'])-1==len(root['sources']))
   catch('reorder-literal-mock-witness',list(reversed(r['forest']))==first['expected_forest'])
   origins=[{'name':'public','module':'Twin','kind':'theorem','axioms':[]},{'name':'_private.Twin.0.p','module':'Twin','kind':'theorem','axioms':[]},{'name':'f.match_1','module':'Twin','kind':'other','axioms':[]}]
   check('clean-twin/origins',I.K.exact_origins(origins,deepcopy(origins)))
   for name,bad in [('missing-origin',origins[:-1]),('duplicate-origin',origins+[origins[0]]),('missing-private-origin',[x for x in origins if not x['name'].startswith('_private')]),('missing-generated-origin',[x for x in origins if '.match_' not in x['name']])]:catch(name,I.K.exact_origins(origins,bad))
   original='import One\ntheorem x : True := True.intro\n';mapped=original.replace('import One','import Two');check('clean-twin/import-only-adapter',mapped.split('\n')[1:],original.split('\n')[1:]);catch('changed-adapter-theorem-body',mapped.replace('True := True.intro','False := by contradiction').split('\n')[1:]==original.split('\n')[1:])
   check('fixed-negative-denominator',sorted(x['id'] for x in negative),sorted(negplan['ids']))
   check('fixed-case-denominators',[len(originals),len(groups),len(E['malformed_original_cases'])],[14,11,8])
  check('bounded-local-enumerations',all(len(x['labels'])<=4 and x['partitions']<=15 for x in I.ENUMERATIONS))
  result.update(status='PASS_PREPARATION_CONTROLS',elapsed_seconds=time.monotonic()-start,original_cases=len(originals),grouped_cases=len(groups),positive_checks=len(checks),negative_catches=len(negative),checks=checks,negatives=negative,details=details,local_enumerations=I.ENUMERATIONS)
 except Exception:
  result.update(status='FAIL_RETAINED',elapsed_seconds=time.monotonic()-start,checks=checks,negatives=negative,details=details,exception=traceback.format_exc());dest.write_text(json.dumps(result,indent=2)+'\n');raise
 dest.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ('status','mode','original_cases','grouped_cases','positive_checks','negative_catches','elapsed_seconds')}))
def CounterSafe(x):return I.Counter(x)
if __name__=='__main__':main()
