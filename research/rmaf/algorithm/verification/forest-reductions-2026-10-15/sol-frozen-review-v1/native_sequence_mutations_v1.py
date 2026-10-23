#!/usr/bin/env python3
"""One-shot native composition and actual-definition corruption twins."""
import json,os,pathlib,subprocess,sys,time
H=pathlib.Path(__file__).resolve().parent;ROOT=H.parents[5];B=H/'isolated';FROZEN=H.parent/'sol-frozen-ready-v1'/'preparation';sys.path.insert(0,str(FROZEN));from graph_controls_v1 import compare_record
spec=json.loads((FROZEN/'TRANSPORT-EXPECTATIONS-v1.json').read_text()); E=spec['mutationExpected']
pre='''import CompletionConsumers
import Consumers
import Lean
open Lean RMAF ForestState
namespace SolNativeExtra
def jTree : Tree → Json
  | .leaf x => toJson x
  | .node l r => Json.arr #[jTree l,jTree r]
def jOpt : Option Tree → Json
  | none => Json.null
  | some t => jTree t
def jTrees (ss : List Tree) : Json := Json.arr (ss.map jTree).toArray
def O : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def SS : List Tree := [.leaf 2,.node (.leaf 0) (.leaf 1)]
def FF : List (List Nat) := [[2],[1,0]]
def CT := cleanupTarget (some O) 2
def CS := cleanupSources SS 2
def CF := cleanupForest FF 2
def QT := CT.map (contract 0 1 3)
def QS := CS.map (contract 0 1 3)
def QF := CF.map (contractBlock 0 1 3)
def ET := QT.map (expand 0 1 3)
def ES := QS.map (expand 0 1 3)
def EF := QF.map (expandBlock 0 1 3)
def RF : List (List Nat) := [2] :: EF
def C : Tree := .node (.leaf 0) (.leaf 1)
def Deep : Tree := .node (.node C (.leaf 2)) (.leaf 3)
def hull := (minimalVertices [0,2] Deep).map (fun v => String.ofList (v.map (fun b => if b then '1' else '0')))
#check @ForestState.singleton_cleanup_forward
#check @ForestState.singleton_cleanup_reverse
'''
def obj(fields):return 'Json.mkObj ['+', '.join('("'+k+'", '+v+')' for k,v in fields.items())+']'
def phase(t,ss,F):return obj({'T':'jOpt '+t,'ss':'jTrees '+ss,'F':'toJson '+F,'cost':'toJson (additionalCost '+ss+' '+F+')','valid':'toJson (agrees '+t+' '+ss+' '+F+')'})
mut=[('hull-unary-erasure','toJson hull','toJson (hull.filter (fun s => s != "00"))'),('source-cost-minus-one','toJson (additionalCost SS FF)','toJson (FF.length - 1)'),('omit-reverse-direction','toJson (["forward","reverse"] : List String)','toJson (["forward"] : List String)'),('fabricated-reconstruction','toJson (agrees (some (.leaf 0)) [.leaf 0] [[0]])','toJson (agrees (some (.leaf 0)) [.leaf 0] [])'),('missing-component-readiness','toJson (cherryReady (some C) [.leaf 0,.leaf 1] 0 1 2)','toJson (cherry 0 1 C)'),('accept-nonfresh-z','toJson (cherryReady (some C) [C] 0 1 1)','toJson (proper (some C) [C] && cherry 0 1 C)'),('drop-surviving-label','toJson (leaves (contract 0 1 3 O))','toJson (leaves (.leaf 3))'),('weak-endpoint-clearance','toJson (disjointVertices (minimalVertices [0,1] C) (minimalVertices [1] C))','toJson (disjointVertices (minimalVertices [0] C) (minimalVertices [1] C))'),('reassignment-cost-equality','toJson (decide (additionalCost [C] (reassignedForest [[0],[1]] [0] 1) = additionalCost [C] [[0],[1]]))','toJson true'),('duplicate-state-labels','toJson (proper (some (.node (.leaf 0) (.leaf 0))) [.leaf 0,.leaf 0])','toJson true')]
source=pre+'\n#eval IO.println ('+obj({'cleanup':phase('CT','CS','CF'),'contract':phase('QT','QS','QF'),'expand':phase('ET','ES','EF'),'reconstructedF':'toJson RF','reconstructedCost':'toJson (additionalCost SS RF)','reconstructedValid':'toJson (agrees (some O) SS RF)','nullValid':'toJson (agrees none [] [])','nullCost':'toJson (additionalCost [] [])','mutations':'Json.arr #['+', '.join(obj({'id':'Json.str "'+n+'"','clean':c,'corrupt':b}) for n,c,b in mut)+']'})+').compress\nend SolNativeExtra\n';(B/'NativeExtra.lean').write_text(source)
t=time.perf_counter();r=subprocess.run([str(ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'),'NativeExtra.lean'],cwd=B,env={**os.environ,'LEAN_PATH':str(B)},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=60);(H/'NativeExtra.log').write_text(r.stdout);assert r.returncode==0,{'exit':r.returncode,'log':'NativeExtra.log'}
actual=json.loads(next(l for l in r.stdout.splitlines() if l.startswith('{')))
for key in ['cleanup','contract','expand']:compare_record(actual[key],{**spec['sequence'][key],'valid':True})
compare_record(sorted(sorted(b) for b in actual['reconstructedF']),sorted(sorted(b) for b in spec['sequence']['reconstructedF']));compare_record(actual['reconstructedCost'],spec['sequence']['reconstructedCost']);compare_record(actual['reconstructedValid'],True);compare_record(actual['nullValid'],spec['emptyNull']['valid']);compare_record(actual['nullCost'],spec['emptyNull']['cost'])
catches=[]
for row in actual['mutations']:
 n=row['id'];clean,bad=row['clean'],row['corrupt']
 if n=='hull-unary-erasure':clean=sorted(clean);bad=sorted(bad)
 compare_record(clean,E[n])
 try:compare_record(bad,E[n])
 except AssertionError as e:catches.append({'id':n,'caught':True,'finding':str(e)})
 else:raise AssertionError('survived '+n)
compare_record(len(catches),10);result={'status':'NATIVE-SEQUENCE-MUTATIONS-PASS','sequence':actual,'mutationsCaught':catches,'seconds':time.perf_counter()-t,'unmodifiedFrozenExpectationFile':str(FROZEN/'TRANSPORT-EXPECTATIONS-v1.json'),'directionControl':'actual singleton forward/reverse signatures compiled by #check; omission mask is the driver-completeness corruption'};(H/'native-extra-v1.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'nativeCorruptionsCaught':len(catches),'seconds':result['seconds']}))
