from pathlib import Path
import json,subprocess,os,time,hashlib,traceback
H=Path(__file__).resolve().parent;R=next(p for p in H.parents if (p/'bootloops-lean').is_file());F=H/'isolated-source-v1';P=H.parent/'frozen-ready-v1/frozen-inputs-v1';D=json.loads((P/'controls-v1.json').read_text());G=json.loads((P/'guard-controls-v1.json').read_text());prior=json.loads((H.parent/'frozen-ready-v1/results/algorithm-output-state-fresh-controls-v1.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def ls(xs):return '['+','.join(ls(x) if isinstance(x,list) else str(x) for x in xs)+']'
def tr(t):return '(.leaf '+str(t)+')' if isinstance(t,int) else '(.node '+tr(t[0])+' '+tr(t[1])+')'
def ot(t):return 'none' if t is None else '(some '+tr(t)+')'
s='''import ActualConsumers
import Lean
open RMAF RestrictionBridge ForestState ForestGroups OutputState
namespace FreshOutputReadouts
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
def treeJson : Tree → Lean.Json
 | .leaf x => Lean.toJson x
 | .node a b => Lean.Json.arr #[treeJson a,treeJson b]
def forestJson (ss : List Tree) : Lean.Json := Lean.Json.arr ((ss.map treeJson).toArray)
def freshRefines (F Q : List (List Nat)) : Bool := F.all fun B => Q.any (contained B)
theorem refines_readout_exact (F Q : List (List Nat)) :
 freshRefines F Q = true ↔ Refines F Q := by
 simp only [freshRefines,Refines,List.all_eq_true,List.any_eq_true,contained_iff]
def printObj (id : String) (fields : List (String × Lean.Json)) : IO Unit :=
 IO.println ("READ|" ++ id ++ "|" ++ (Lean.Json.mkObj fields).compress)
def literal (id : String) (S T : Tree) (Q F : List (List Nat)) : IO Unit := do
 let ss := sourceForest S Q
 printObj id [("sources",forestJson ss),("source_count",Lean.toJson ss.length),
 ("Q_checked",Lean.toJson (partitionCheck (leaves S) Q)),
 ("source_Q_clear",Lean.toJson (pairwiseEmbeddings S Q)),("target_Q_clear",Lean.toJson (pairwiseEmbeddings T Q)),
 ("state",Lean.toJson (agrees (some T) ss F)),("original_AF",Lean.toJson (agreement T S F)),
 ("refines",Lean.toJson (freshRefines F Q)),("additional",Lean.toJson (additionalCost ss F)),
 ("Q_subtraction",Lean.toJson (F.length-Q.length)),("proper",Lean.toJson (proper (some T) ss))]
def guard (id : String) (T : Option Tree) (ss : List Tree) (F : List (List Nat)) : IO Unit :=
 printObj id [("proper",Lean.toJson (proper T ss)),("state",Lean.toJson (agrees T ss F)),("additional",Lean.toJson (additionalCost ss F))]
def priorityBool (T : Tree) (a : Tree) (bs cs : List Tree) : Bool :=
 bs.all (fun b => disjointVertices (minimalVertices (leaves a) T) (minimalVertices (leaves b) T)) &&
 cs.all (fun c => disjointVertices (minimalVertices (leaves a) T) (minimalVertices (leaves c) T)) &&
 bs.all (fun b => cs.all (fun c => disjointVertices (minimalVertices (leaves b) T) (minimalVertices (leaves c) T)))
'''
for c in D['literal_cases']:
 f=D['fixtures'][c['fixture']];s+=f'\n#eval literal {json.dumps(c["id"])} {tr(f["S"])} {tr(f["T"])} {ls(c.get("Q",f["Q"]))} {ls(c["F"])}\n'
for c in G:s+=f'\n#eval guard {json.dumps("guard."+c["id"])} {ot(c["T"])} [{",".join(tr(x) for x in c["sources"])}] {ls(c["F"])}\n'
for bank in prior['partition_banks']:
 f=D['fixtures'][bank['fixture']]
 for i,row in enumerate(bank['rows']):s+=f'\n#eval literal {json.dumps("bank."+bank["fixture"]+"."+str(i))} {tr(f["S"])} {tr(f["T"])} {ls(f["Q"])} {ls(row["F"])}\n'
d=D['grouping'];f=D['fixtures'][d['fixture']]
s+=f'''\ndef groupS : Tree := {tr(f['S'])}
def groupT : Tree := {tr(f['T'])}
def groupQ : List (List Nat) := {ls(f['Q'])}
def groupA : List Nat := {ls(d['A'])}
def groupB : List Nat := {ls([x for b in d['B'] for x in b])}
def groupC : List Nat := {ls(d['C'])}
def fa : List (List Nat) := {ls(d['FA'])}
def fc : List (List Nat) := {ls(d['FC'])}
def fbSingles : List (List Nat) := {ls(d['Bsingletons'])}
def fbCheap : List (List Nat) := {ls(d['Bcheaper'])}
def groupSs := sourceForest groupS groupQ
def groupBs := owned groupSs groupB
def groupAs := owned groupSs groupA
def groupCs := owned groupSs groupC
#eval printObj "group" [
 ("A_cost",Lean.toJson (additionalCost groupAs fa)),("C_cost",Lean.toJson (additionalCost groupCs fc)),
 ("B_singletons_cost",Lean.toJson (additionalCost groupBs fbSingles)),("B_cheaper_cost",Lean.toJson (additionalCost groupBs fbCheap)),
 ("parent_singletons_cost",Lean.toJson (additionalCost groupSs (fa++fbSingles++fc))),
 ("parent_cheaper_cost",Lean.toJson (additionalCost groupSs (fa++fbCheap++fc))),
 ("B_internal_target_clear",Lean.toJson (pairwiseEmbeddings groupT {ls(d['B'])})),
 ("cross_group_clear",Lean.toJson ((decide (groupAs.length = 1) && groupAs.all (fun a => priorityBool groupT a groupBs groupCs)))),
 ("source_permutation",Lean.toJson (decide (groupSs.Perm (groupAs++groupBs.reverse++groupCs)))),
 ("actual_sideOutputs_derived",Lean.toJson false),("recursive_solver_implemented",Lean.toJson false)]
#eval guard "local.A" (localTarget (some groupT) groupA) groupAs fa
#eval guard "local.C" (localTarget (some groupT) groupC) groupCs fc
#eval guard "local.Bsingletons" (localTarget (some groupT) groupB) groupBs fbSingles
#eval guard "local.Bcheaper" (localTarget (some groupT) groupB) groupBs fbCheap
-- Instrument-only supplied table. This definition does not assert ResidualSolverContract.
def mock (id : String) (q : Nat) (hasContract groupsOk : Bool) (answer : Option (List (List Nat))) : IO Unit := do
 let access := (q>0) && hasContract && groupsOk
 let fb := if access then answer else none
 let witness := fb.isSome
 let cost := fb.map (additionalCost groupBs)
 let total := fb.map (fun f => additionalCost groupSs (fa++f++fc))
 let checked := fb.all (fun f => agrees (localTarget (some groupT) groupB) groupBs f && decide (additionalCost groupBs f ≤ q-1) && agrees (some groupT) groupSs (fa++f++fc))
 if !checked then throw (IO.userError "mock supplied witness invalid")
 printObj id [("access",Lean.toJson access),("calls",Lean.toJson (if access then 1 else 0 : Nat)),
 ("child_budget",Lean.toJson (if access then some (q-1) else none)),("witness",Lean.toJson witness),
 ("child_cost",Lean.toJson cost),("parent_cost",Lean.toJson total)]
'''
for c in d['mock_calls']:
 ans='none' if c['choice'] is None else 'some '+ls(d[c['choice']]);s+=f'\n#eval mock {json.dumps("mock."+c["id"])} {c["q"]} {str(c["contract"]).lower()} {str(c["groups_ok"]).lower()} ({ans})\n'
s+='''\n#check OutputState.checked_materialization
#check OutputState.sourceForest_proper
#check OutputState.exact_additional_cost
#check OutputState.agrees_iff_original
#check OutputState.generated_source_bridge
#check OutputState.opposite_grouping
#check OutputState.opposite_local_certificates
#check OutputState.every_opposite_residual_query
end FreshOutputReadouts
'''
(F/'FreshActualReadoutsV2.lean').write_text(s);env=os.environ.copy();env['LEAN_PATH']=str(F);start=time.monotonic()
p=subprocess.run([str(R/'bootloops-lean'),'-o','FreshActualReadoutsV2.olean','FreshActualReadoutsV2.lean'],cwd=F,env=env,capture_output=True,text=True,timeout=30);log=p.stdout+p.stderr;(F/'FreshActualReadoutsV2.log').write_text(log)
assert p.returncode==0,log[-6000:]
readouts={}
for line in log.splitlines():
 if line.startswith('READ|'):
  _,key,payload=line.split('|',2);assert key not in readouts;readouts[key]=json.loads(payload)
comparisons=[]
def eq(name,a,b):
 row={'id':name,'actual':a,'expected':b,'pass':a==b};comparisons.append(row);assert row['pass'],row
for c in D['literal_cases']:
 for k,v in c['expected'].items():eq(c['id']+'.'+k,readouts[c['id']][k],v)
for c in G:
 for k,v in c['expected'].items():eq('guard.'+c['id']+'.'+k,readouts['guard.'+c['id']][k],v)
for bank in prior['partition_banks']:
 for i,row in enumerate(bank['rows']):
  actual=readouts['bank.'+bank['fixture']+'.'+str(i)]
  eq('partition.'+bank['fixture']+'.'+str(i)+'.state',actual['state'],row['state'])
  eq('partition.'+bank['fixture']+'.'+str(i)+'.original_refinement',actual['original_AF'] and actual['refines'],row['original_refinement'])
  eq('partition.'+bank['fixture']+'.'+str(i)+'.cost',actual['additional'],row['additional'])
for k,v in d['expected'].items():eq('group.'+k,readouts['group'][k],v)
for c in d['mock_calls']:
 for k,v in c['expected'].items():eq('mock.'+c['id']+'.'+k,readouts['mock.'+c['id']][k],v)
for key,cost in [('A',1),('C',0),('Bsingletons',2),('Bcheaper',1)]:
 eq('local.'+key+'.state',readouts['local.'+key]['state'],True);eq('local.'+key+'.cost',readouts['local.'+key]['additional'],cost)
expectedkeys=24+7+30+1+4+6;assert len(readouts)==expectedkeys
out={'verdict':'PASS_ACTUAL_COMPILED_READOUTS_AGAINST_FROZEN_CONTROLS','seconds':time.monotonic()-start,'readout_denominator':len(readouts),'comparison_denominator':len(comparisons),'comparisons_passed':sum(x['pass'] for x in comparisons),'readouts':readouts,'comparisons':comparisons,'mock_contract_status':'INSTRUMENT_ONLY; no recursive contract or implementation claimed','all_main_milestones':'OPEN'}
(R/'research/rmaf/results/algorithm-output-state-fresh-actual-readouts-v2.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['verdict','seconds','readout_denominator','comparison_denominator','comparisons_passed']}))
