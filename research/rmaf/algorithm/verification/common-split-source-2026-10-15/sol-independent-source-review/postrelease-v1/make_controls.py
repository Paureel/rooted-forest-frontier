#!/usr/bin/env python3
"""Postcontact interface adapter for exactly the frozen old24 fixtures."""
import hashlib,json,pathlib
P=pathlib.Path(__file__).resolve().parent
OLD=P.parent/'OWN-X0-REUSE-v1.json'; DATA=json.loads(OLD.read_text())
C=P/'actual-controls';C.mkdir(exist_ok=True)
def tree(t):return f'(.leaf {t})' if isinstance(t,int) else f'(.node {tree(t[0])} {tree(t[1])})'
def ll(x):return '['+','.join(ll(v) if isinstance(v,list) else str(v) for v in x)+']'
def vertex(s):return '['+','.join('false' if b=='0' else 'true' for b in s)+']'
def restrict(t,x):
 if isinstance(t,int):return t if t in x else None
 a,b=restrict(t[0],x),restrict(t[1],x)
 return b if a is None else a if b is None else [a,b]
def at(t,p):
 for b in p:t=t[int(b)]
 return t
BASE='''import DerivedMinimum
import Lean.Data.Json
open RMAF OrdinaryCommonSplit Universal233.DepthOne Universal233.CoreGraph Lean
namespace OwnReadout
def smallCert (t s : Tree) (m : Nat) : Bool :=
  match pretest01 t s with
  | .found c => decide (cutCost c=m)
  | _ => false
theorem smallCert_minimum (t s : Tree) (m : Nat) (h : smallCert t s m=true) :
    IsMinimum t s m := by
  cases e : pretest01 t s with
  | refused => simp [smallCert,e] at h
  | rejected => simp [smallCert,e] at h
  | found c =>
    have eq : cutCost c=m := by simpa [smallCert,e] using h
    obtain ⟨ha,hc,lower⟩ := found_globally_minimum t s c e
    exact ⟨⟨forest s c,ha,hc.trans eq⟩,fun f hf => eq ▸ lower f hf⟩
def jt : Tree → Json
  | .leaf x => toJson x
  | .node l r => Json.arr #[jt l,jt r]
def restriction (t : Tree) (x : List Nat) : Json :=
  match restrict x t with | none => Json.null | some u => jt u
def markedJson (t : Tree) (x : List Nat) (y r : Nat) : Json :=
  match marked t x y r with | none => Json.null | some u => jt u
def finiteAFs (t s : Tree) : List (List (List Nat)) :=
  let labels := leaves t
  ((assignments labels.length labels.length).map fun a =>
    (blocks a).map (fun b => b.map (fun i => labels[i]!))).filter (agreement t s)
def pretestJson (t s : Tree) : Json :=
  match pretest01 t s with
  | .refused => Json.str "refused"
  | .rejected => Json.str "rejected"
  | .found c => Json.mkObj [("cost",toJson (cutCost c)),("forest",toJson (forest s c)),
      ("agreement",toJson (agreement t s (forest s c))),("cut",toJson c)]
def pairJson (t s : Tree) : Json := Json.mkObj [
  ("T",jt t),("S",jt s),("proper",toJson (proper t s)),
  ("pretest",pretestJson t s),("all_af_encodings",toJson (finiteAFs t s))]
end OwnReadout
'''
(C/'OwnReadout.lean').write_text(BASE)
index=[]
for i,c in enumerate(DATA['cases']):
 e=c['expected'];T,S=e['T'],e['S'];X,Y=e['X'],e['Y'];x,y=e['reps'];rho,gamma=e['markers'];m,n,mr,ng=e['costs'][1:]
 trees=[T,S,restrict(T,X),restrict(S,X),restrict(T,Y),restrict(S,Y)]+e['marked_trees']
 names=['t','s','tx','sx','ty','sy','mxt','mxs','myt','mys'];mod=f'OwnCase{i:02d}'
 text='import OwnReadout\nopen RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout\nnamespace '+mod+'\n'
 for name,t in zip(names,trees):text+=f'def {name} : Tree := {tree(t)}\n'
 text+=f'def xs : List Nat := {ll(X)}\ndef ys : List Nat := {ll(Y)}\n'
 for which,t,edges in [('t',T,e['edges_T']),('s',S,e['edges_S'])]:
  _,p,side=edges[0];u=at(t,p);disj='Or.inl' if side=='Y' else 'Or.inr'
  text+=f'theorem edge_{which} : OriginalSplit {which} xs ys :=\n  ⟨{vertex(p)},{tree(u)},by decide,by decide,{disj} (by decide)⟩\n'
 for j,(a,b,z) in enumerate([('tx','sx',m),('ty','sy',n),('mxt','mxs',mr),('myt','mys',ng)]):
  text+=f'theorem local{j} : IsMinimum {a} {b} {z} := smallCert_minimum _ _ _ (by decide)\n'
 text+=f'''theorem derived_global : IsMinimum t s {e['costs'][0]} := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    {x} {y} {rho} {gamma} {m} {n} {mr} {ng}
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
def readout : Lean.Json := Lean.Json.mkObj [
  ("id",Lean.Json.str {json.dumps(c['id'])}),
  ("restrictions",Lean.Json.arr #[restriction t xs,restriction s xs,restriction t ys,restriction s ys]),
  ("marked",Lean.Json.arr #[markedJson t xs {y} {rho},markedJson s xs {y} {rho},
    markedJson t ys {x} {gamma},markedJson s ys {x} {gamma}]),
  ("pairs",Lean.Json.arr #[pairJson t s,pairJson tx sx,pairJson ty sy,pairJson mxt mxs,pairJson myt mys]),
  ("hulls",Lean.toJson (({ll(e['minima'][0])} : List (List (List Nat))).map fun f =>
     f.map fun b => (minimalVertices b t,minimalVertices b s))),
  ("identity_value",Lean.toJson (commonSplitValue {m} {n} {mr} {ng}))]
end {mod}
def main : IO Unit := IO.println {mod}.readout.compress
'''
 (C/(mod+'.lean')).write_text(text)
 index.append({'module':mod,'case_id':c['id'],'source_sha256':hashlib.sha256(text.encode()).hexdigest(),'expected':e,'fixed_old_source':str(OLD),'old_source_sha256':hashlib.sha256(OLD.read_bytes()).hexdigest()})
(P/'ACTUAL-CONTROL-REGISTRY-v1.json').write_text(json.dumps(index,indent=2,sort_keys=True)+'\n')
(P/'ACTUAL-CONTROL-PIN-v1.json').write_text(json.dumps({'phase':'POSTCONTACT adapter; zero extra replication','old_cases':len(index),'same_frozen_expectations':True,'no_census_extension':True,'local_witness_certificate':'actual released pretest01 found_globally_minimum (cost0/1 only)','global_certificate':'actual common_split_derived_minimum applied to four certified local witnesses','output_scope':'actual fixed-instance finite AF/trees/hulls/pretest readouts; no general caller implementation','adapter_hash':hashlib.sha256(BASE.encode()).hexdigest()},indent=2)+'\n')
print('generated',len(index),'fixed old controls')
