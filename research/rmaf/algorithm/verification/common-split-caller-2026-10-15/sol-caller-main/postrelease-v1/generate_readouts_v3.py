import copy,hashlib,importlib.util,json,pathlib
P=pathlib.Path(__file__).resolve().parent;PRE=P.parent
s=importlib.util.spec_from_file_location('ownpregraph',PRE/'scoped_graph_v2.py');g=importlib.util.module_from_spec(s);s.loader.exec_module(g)
def tree(t):return '(.leaf '+str(t)+')' if type(t)is int else '(.node '+tree(t[0])+' '+tree(t[1])+')'
def ls(x):return '['+','.join(ls(a) if isinstance(a,(tuple,list)) else str(a).lower() if isinstance(a,bool) else str(a) for a in x)+']'
def subtree(t,p):
 for a in p:t=t[int(a)]
 return t
def edge(e,which):
 p=e['cut'+which];u=subtree(e[which],p);side='inl' if set(g.g.leaves(g.g.tree(u)))==set(e['Y']) else 'inr'
 return '⟨'+ls([a=='1' for a in p])+','+tree(u)+',by decide,by decide,Or.'+side+' (by decide)⟩'
def setup(n,e):
 d=g.setup(e);ts=d['trees'];fields={'T':e['T'],'S':e['S'],'tx':ts['TX'],'sx':ts['SX'],'ty':ts['TY'],'sy':ts['SY'],'mxT':ts['TMX'],'mxS':ts['SMX'],'myT':ts['TMY'],'myS':ts['SMY']};out='def d'+str(n)+' : Setup := {\n'
 for k,v in fields.items():out+='  '+k+' := '+tree(v)+'\n'
 for k,v in [('X',e['X']),('Y',e['Y'])]:out+='  '+k+' := '+ls(v)+'\n'
 for k,v in [('x',e['repX']),('y',e['repY']),('rho',e['rho']),('gamma',e['gamma'])]:out+='  '+k+' := '+str(v)+'\n'
 out+='  edgeT := '+edge(e,'T')+'\n  edgeS := '+edge(e,'S')+'\n'
 for k in ['nt','ns','hpT','hpS','htx','hsx','hty','hsy','hMXT','hMXS','hMYT','hMYS','hx','hy','frT','frS','fgT','fgS']:out+='  '+k+' := by decide\n'
 return out+'}\n'
from case_inputs_v3 import cases
# No complete family is regenerated as a reference. Callback literal families are the frozen hand choices.
head='''import GuardedExact
import Lean
open Lean RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller Universal233
namespace IndependentCallerReadout
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
def jt : Tree → Json
 | .leaf n => toJson n
 | .node a b => toJson [jt a,jt b]
def jjob (j : Job) : Json := Json.mkObj [("T",jt j.T),("S",jt j.S),("budget",toJson j.budget)]
def jp (T S : Tree) : Json :=
 match hp : DepthOne.pretest01 T S with
 | .refused => Json.mkObj [("status",toJson "REFUSED")]
 | .rejected => Json.mkObj [("status",toJson "REJECT")]
 | .found p => Json.mkObj [("status",toJson (if p.isNone then "FOUND0" else "FOUND1")),("cut",toJson p),("forest",toJson (DepthOne.forest S p))]
def reply (d : Setup) (FX FM : Forest) (T S : Tree) (r : Nat) : Option Forest :=
 let F := if T==d.tx && S==d.sx then FX else FM
 if F.length-1≤r then some F else none
def cb (tag : String) (q : Nat) (d : Setup) (FX FM : Forest) (T S : Tree) (r : Nat) : Option Forest :=
 dbgTrace ("TRACE|"++tag++"|"++toString q++"|"++(if T==d.tx && S==d.sx then "ordinaryX" else if T==d.mxT && S==d.mxS then "markedX" else "UNPAID")++"|"++toString r)
   (fun _ => reply d FX FM T S r)
def row (tag : String) (d : Setup) (q : Nat) (FX FM : Forest) : IO Unit := do
 let result := runGuarded d q (cb tag q d FX FM)
 let FY := match DepthOne.pretest01 d.ty d.sy with | .found c => DepthOne.forest d.sy c | _ => []
 let FN := outsideReply d FY
 let cand := match FN with | none => [] | some F => mergeCandidates d.X d.Y d.x d.y d.rho d.gamma FM F
 let hulls := fun T => (FX++FY).map (minimalVertices · T)
 IO.println <| (Json.mkObj [("id",toJson tag),("q",toJson q),("result",toJson result),("status",toJson (match result with | none => "REFUSAL" | some none => "BOUNDED_NEGATIVE" | some (some _) => "MINIMUM")),
   ("callback_replies",toJson ((guardedJobs d q).map (fun j => reply d FX FM j.T j.S j.budget))),("planned_jobs",toJson ((guardedJobs d q).map jjob)),("mass",toJson (toString (guardedMass (233/100) d q))),
   ("trees",toJson [jt d.tx,jt d.sx,jt d.ty,jt d.sy,jt d.mxT,jt d.mxS,jt d.myT,jt d.myS]),
   ("outside",jp d.ty d.sy),("marked_outside",jp d.myT d.myS),("FY",toJson FY),("FN",toJson FN),
   ("FX",toJson FX),("FM",toJson FM),("candidate_multiset",toJson cand),
   ("valid_candidates",toJson (cand.filter (agreement d.T d.S))),
   ("pick",toJson (pickMerge d.T d.S d.X d.Y d.x d.y d.rho d.gamma FM (FN.getD []))),
   ("reconstructed",toJson (reconstruct d FX FY FM (FN.getD []))),
   ("concatenation_valid",toJson (agreement d.T d.S (FX++FY))),
   ("concatenation_hulls_T",toJson (hulls d.T)),("concatenation_hulls_S",toJson (hulls d.S))]).compress
'''
head += '''def witness (tag : String) (d : Setup) (F : Forest) : IO Unit :=
 IO.println <| (Json.mkObj [("kind",toJson "WITNESS"),("id",toJson tag),("forest",toJson F),("agreement",toJson (agreement d.T d.S F)),("hulls_T",toJson (F.map (minimalVertices · d.T))),("hulls_S",toJson (F.map (minimalVertices · d.S)))]).compress
'''
text=head
for i,e in enumerate(cases):text+=setup(i,e)
text+='def main : IO Unit := do\n'
for i,e in enumerate(cases):
 for q in e['answers']:
  for j in [0]:
   FX=g.callback_fixture(e,'X',100);FM=g.callback_fixture(e,'MX',100)
   text+='  row '+json.dumps(e['id'])+' d'+str(i)+' '+q+' '+ls(FX)+' '+ls(FM)+'\n'
for i,e in enumerate(cases):
 if 'hulls' in e:text+='  witness '+json.dumps(e['id'])+' d'+str(i)+' '+ls(e['hulls']['forest'])+'\n'
text+='end IndependentCallerReadout\ndef main := IndependentCallerReadout.main\n'
(P/'Readouts_v3.lean').write_text(text)
(P/'READOUT-PINS-v3.json').write_text(json.dumps({'source_sha256':hashlib.sha256(text.encode()).hexdigest(),'generator_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'frozen_inputs':{n:hashlib.sha256((PRE/n).read_bytes()).hexdigest() for n in ['EXPECTATIONS-v1.json','EXPECTATIONS-EXTENSION-v2.json','scoped_graph_v2.py']}},indent=2)+'\n')
print('generated',len(cases),'cases',sum(len(e['answers']) for e in cases),'rows')
