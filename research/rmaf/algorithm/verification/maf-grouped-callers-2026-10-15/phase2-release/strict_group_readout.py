"""Actual executable callers/grouped filters against immutable prerelease data."""
from pathlib import Path
from fractions import Fraction
import importlib.util,json,sys
sys.dont_write_bytecode=True
import rebuild as R
PRE=R.HERE.parent
spec=importlib.util.spec_from_file_location('own_frozen_maf_groups',PRE/'instrument.py');I=importlib.util.module_from_spec(spec);spec.loader.exec_module(I)
E=json.loads((PRE/'EXPECTATIONS-v1.json').read_text())
def lit(v):return '['+', '.join(lit(x) for x in v)+']' if isinstance(v,list) else str(v)
def tree(t):return f'(Tree.leaf {t})' if type(t) is int else f'(Tree.node {tree(t[0])} {tree(t[1])})'
def opt(t):return 'none' if t is None else '(some '+tree(t)+')'
def trees(ts):return '['+', '.join(tree(t) for t in ts)+']'
def emit(k,x):return '#eval IO.println ("'+k+'|" ++ ('+x+').compress)\n'
COMMON='''import Lean
open RMAF Lean
def treeJSON : Tree → Json
 | .leaf x => toJson x
 | .node a b => Json.arr #[treeJSON a,treeJSON b]
def optJSON (t : Option Tree) : Json := match t with | none => Json.null | some s => treeJSON s
def ratJSON (r : Rat) : Json := Json.mkObj [("num",toJson r.num),("den",toJson r.den)]
'''
def execute(arm,text):
 b=R.HERE/('isolated-'+arm);(b/'FreshReadout.lean').write_text(text);run=R.helper().run(b,'FreshReadout',['-o','FreshReadout.olean']);assert run['exit']==0,run
 actual={}
 for s in (b/'FreshReadout.log').read_text().splitlines():
  if s.startswith('CASE:') or s.startswith('BAD:') or s.startswith('CHILD:') or s.startswith('DUPLICATE:'):
   k,v=s.split('|',1);assert k not in actual;actual[k]=json.loads(v)
 return actual,run

def maf():
 text='import OriginalPaid\n'+COMMON+'''open Universal233 PaidQueries MafScheduler
def jobJSON : Job (List Nat) Forest → Json
 | .hard U => Json.mkObj [("kind",toJson "hard"),("problem",toJson U)]
 | .resolved U c F => Json.mkObj [("kind",toJson "resolved"),("problem",toJson U),("cost",toJson c),("forest",toJson F)]
def prepJSON (p : Option (List (Job (List Nat) Forest))) : Json :=
 match p with | none => Json.null | some js => toJson (js.map jobJSON)
def preJSON (t s : Tree) : Json := match DepthOne.pretest01 t s with
 | .refused => toJson "refused"
 | .rejected => toJson "rejected"
 | .found c => Json.mkObj [("cost",toJson (DepthOne.cutCost c)),("forest",toJson (DepthOne.forest s c))]
def callerJSON (T S : Tree) (Q : Forest) (q : Nat) (solve : Tree → Tree → Nat → Option Forest) : Json :=
 let prep := prepare T S Q
 let a := attempt T S solve q Q
 let met := prep.map (meterSchedule (recursive T S solve) (fun U b => 1000*U.length+b) q)
 Json.mkObj [("prepare",prepJSON prep),("pretests",toJson (Q.map (fun U => match restrict U T,restrict U S with | some t,some s => preJSON t s | _,_ => Json.null))),
  ("restrictions",toJson (Q.map (fun U => Json.arr #[optJSON (restrict U T),optJSON (restrict U S)]))),
  ("proper_blocks",toJson (Q.map (properBlock T S))),
  ("forest",toJson (solveDisjoint T S solve q Q)),("calls",toJson (calls T S solve q Q)),
  ("bad_parents",toJson (badParents T S Q)),
  ("mass2",ratJSON (actualQueryMass 2 q (calls T S solve q Q))),
  ("mass233",ratJSON (actualQueryMass (233/100) q (calls T S solve q Q))),
  ("meter_queries",toJson ((met.map (fun r => r.queries.map (fun p => Json.mkObj [("problem",toJson p.1),("budget",toJson p.2)]))).getD [])),
  ("recursive_charge",toJson ((met.map (·.recursiveWork)).getD 0)),
  ("meter_caller_work",toJson ((met.map (·.callerWork)).getD 0)),
  ("source_target_Q_guards",toJson [decide (leaves T).Nodup,decide (leaves S).Nodup,partitionCheck (leaves T) Q,partitionCheck (leaves S) Q,pairwiseEmbeddings T Q,pairwiseEmbeddings S Q])]
'''
 for j,c in enumerate(E['original_cases']):
  text+=f'def T{j} : Tree := {tree(c["target"])}\ndef S{j} : Tree := {tree(c["source"])}\n'
  body='none'
  for k in reversed(range(len(c['Q']))):
   U=c['Q'][k];t=tree(I.restrict(c['target'],U));s=tree(I.restrict(c['source'],U));F=lit(c['witnesses'][k]);ret='none' if c.get('fail_slot')==k else f'(if ({F} : Forest).length-1 ≤ b then some {F} else none)'
   body=f'if t = {t} ∧ s = {s} then {ret} else ({body})'
  text+=f'def callback{j} (t s : Tree) (b : Nat) : Option Forest := {body}\n'
  text+=emit('CASE:'+c['id'],f'callerJSON T{j} S{j} {lit(c["Q"])} {c["q"]} callback{j}')
 for c in E['malformed_original_cases']:
  text+=emit('BAD:'+c['id'],f'callerJSON {tree(c["target"])} {tree(c["source"])} {lit(c["Q"])} 5 (fun _ _ _ => none)')
 text+=emit('DUPLICATE:generic-slots','toJson ((schedule (fun (_ : String) (_ : Nat) => some (2,(0 : Nat))) 4 [Job.hard "same",Job.hard "same"]).calls)')
 actual,run=execute('maf',text);checks=[];qualifications=[];cases={}
 def check(n,a,e):checks.append({'id':n,'pass':a==e});assert a==e,(n,a,e)
 for c in E['original_cases']:
  n=c['id'];a=actual['CASE:'+n];ref=I.run_caller(c);cases[n]=a
  check(n+'/actual-original-Q-guards',all(a['source_target_Q_guards']),True)
  check(n+'/literal-call-budgets',a['calls'],[x['budget'] for x in c['expected_calls']])
  check(n+'/actual-prepared-problems',[x['problem'] for x in a['prepare']],c['Q'])
  check(n+'/proper-requested-blocks',a['proper_blocks'],[True]*len(c['Q']))
  for k,(U,j,pre) in enumerate(zip(c['Q'],a['prepare'],a['pretests'],strict=True)):
   minimum=c['local_minima'][k];check(n+f'/restrictions{k}',a['restrictions'][k],[I.restrict(c['target'],U),I.restrict(c['source'],U)])
   check(n+f'/slot-kind{k}',j['kind'],'hard' if minimum>=2 else 'resolved')
   if minimum<=1:
    check(n+f'/stored-cost{k}',j['cost'],minimum);check(n+f'/stored-valid{k}',I.agreement(I.restrict(c['source'],U),I.restrict(c['target'],U),j['forest']),True)
    if j['forest']!=c['witnesses'][k]:qualifications.append({'id':n,'slot':k,'kind':'permitted depth1 minimum tie class','frozen_mock':c['witnesses'][k],'actual':j['forest'],'expectations_changed':False})
   else:check(n+f'/actual-depth1-reject{k}',pre,'rejected')
  if not any(q['id']==n for q in qualifications):check(n+'/literal-concatenation',a['forest'],c['expected_forest'])
  else:check(n+'/success-tie-class',a['forest'] is not None,c['expected_forest'] is not None)
  if a['forest'] is not None:
   check(n+'/actual-global-witness',I.agreement(c['source'],c['target'],a['forest']),True);check(n+'/additional-cost',len(a['forest'])-len(c['Q']),c['expected_additional']);check(n+'/original-cost',len(a['forest'])-1,c['expected_original_cuts'])
  queries=[{'problem':c['Q'][r['slot']],'budget':r['budget']} for r in c['expected_calls']]
  check(n+'/actual-meter-problem-occurrences',a['meter_queries'],queries)
  check(n+'/actual-exact-recursive-charge',a['recursive_charge'],sum(1000*len(x['problem'])+x['budget'] for x in queries))
  check(n+'/meter-caller-envelope',a['meter_caller_work']<=32*(len(c['Q'])+1),True)
  for base,key in [(Fraction(2),'mass2'),(Fraction(233,100),'mass233')]:check(n+'/'+key,Fraction(a[key]['num'],a[key]['den']),I.normalized_mass(c['expected_calls'],c['q'],base))
 for c in E['malformed_original_cases']:
  a=actual['BAD:'+c['id']];check(c['id']+'/original-theorem-guards',all(a['source_target_Q_guards']),c['valid'])
  if c['id'] in ('absent-request','duplicate-request-label','empty-request'):check(c['id']+'/explicit-properBlock-refusal',a['prepare'],None)
 check('duplicate-problem-occurrences',actual['DUPLICATE:generic-slots'],[2,2])
 out={'status':'PASS_ACTUAL_ORIGINAL_CALLER_READOUT','build':run,'comparisons':len(checks),'checks':checks,'actual':actual,'cases':cases,'tie_class_qualifications':qualifications,'expectations_changed':False,'all_main_milestones':'OPEN','replication_count_added':0}
 p=R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-maf-readout-v1.json';p.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],len(checks),len(qualifications))

def groups():
 text='import GroupPriority\n'+COMMON+'''open ForestState ForestGroups RestrictionBridge
 def ownsBool (ss : List Tree) (Q : List (List Nat)) : Bool := ss.all (fun s => Q.any (contained (leaves s)))
 def crossBool (T : Option Tree) (ss : List Tree) (Q : List (List Nat)) : Bool := match T with
 | none => true
 | some t => Q.all (fun U => Q.all (fun V => if U=V then true else
    (owned ss U).all (fun s => (owned ss V).all (fun r => disjointVertices (minimalVertices (leaves s) t) (minimalVertices (leaves r) t)))))
 def groupJSON (T : Option Tree) (ss : List Tree) (Q F : List (List Nat)) : Json := Json.mkObj [
 ("proper",toJson (proper T ss)),("checked_Q",toJson (partitionCheck (labels T) Q)),("ownership",toJson (ownsBool ss Q)),
 ("cross",toJson (crossBool T ss Q)),("global_agrees",toJson (agrees T ss F)),("additional",toJson (additionalCost ss F)),
 ("whole_group_disjoint",toJson (targetEmbeddings T Q)),
 ("within",toJson (match T with | none => false | some t => Q.any (fun U => !(pairwiseEmbeddings t ((owned ss U).map leaves))))),
 ("local",toJson (Q.map (fun U => Json.mkObj [("target",optJSON (localTarget T U)),("sources",toJson ((owned ss U).map treeJSON)),
   ("indices",toJson (((ss.zipIdx).filter (fun si => contained (leaves si.1) U)).map Prod.snd)),
   ("forest",toJson (family U F)),("agrees",toJson (agrees (localTarget T U) (owned ss U) (family U F))),
   ("cost",toJson (additionalCost (owned ss U) (family U F)))])))]
'''
 for c in E['grouped_cases']:text+=emit('CASE:'+c['id'],f'groupJSON {opt(c["target"])} {trees(c["sources"])} {lit(c["Q"])} {lit(c["F"])}')
 actual,run=execute('groups',text);checks=[];mismatches=[]
 def check(n,a,e):checks.append({'id':n,'pass':a==e});assert a==e,(n,a,e)
 for c in E['grouped_cases']:
  n=c['id'];a=actual['CASE:'+n];ref=I.grouped(c['target'],c['sources'],c['Q'],c['F'])
  for key in ('proper','checked_Q','ownership','global_agrees','additional','whole_group_disjoint','within'):check(n+'/'+key,a[key],ref[key])
  if a['cross']!=ref['cross']:
   mismatches.append({'id':n,'field':'cross','frozen_expected':ref['cross'],'actual':a['cross'],'Owns_premise':a['ownership'],'expectations_changed':False,'diagnosis':'Frozen reference forces false for an unowned source; actual CrossClear quantifies ONLY owned pairs and may hold without Owns. Outside reverse theorem premises; retain mismatch, not a source theorem refutation.'})
  else:check(n+'/cross',a['cross'],ref['cross'])
  check(n+'/literal-owned-local-families',a['local'],[{k:x[k] for k in ('target','sources','indices','forest','agrees','cost')} for x in ref['local']])
 assert mismatches==[{'id':'missing-whole-source-ownership','field':'cross','frozen_expected':False,'actual':True,'Owns_premise':False,'expectations_changed':False,'diagnosis':'Frozen reference forces false for an unowned source; actual CrossClear quantifies ONLY owned pairs and may hold without Owns. Outside reverse theorem premises; retain mismatch, not a source theorem refutation.'}],mismatches
 out={'status':'FAIL_RETAINED_STRICT_FROZEN_GROUP_CROSS_EXPECTATION','build':run,'comparisons':len(checks),'checks':checks,'actual':actual,'reference_mismatches':mismatches,'expectations_changed':False,'all_main_milestones':'OPEN','replication_count_added':0}
 p=R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-groups-readout-v1.json';p.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],len(checks),len(mismatches));raise AssertionError('FROZEN_GROUP_CROSS_MISMATCH_RETAINED')
if __name__=='__main__':{'maf':maf,'groups':groups}[sys.argv[1]]()
