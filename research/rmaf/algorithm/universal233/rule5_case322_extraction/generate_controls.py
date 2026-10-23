#!/usr/bin/env python3
"""One-shot author Lean fixture materializer; pinned fixed trees, no AF search."""
from pathlib import Path
import controls
D=Path(__file__).resolve().parent;L=controls.L;A=controls.A
ids=dict(a=0,b=1,c=2,w=3,t=4,x=5,p=6,q=7,y=8,z=9,s=10)
def ts(t):return f'.leaf {ids[t]}' if isinstance(t,str) else f'(.node ({ts(t[0])}) ({ts(t[1])}))'
def vs(s):return '['+','.join('true' if x=='1' else 'false' for x in s)+']'
family=A.fixtures();family['core']=((((('x',(('a','b'),'s')),'y'),'c'),'z'),(((('a',('x',('y','z'))),'c'),'b'),'s'),[2,1,4])
txt='import CurrentPartition\nnamespace Universal233.Case322Extraction.Controls\nopen RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching\nopen Universal233.Rule5Local Universal233.Rule5Case322 Universal233.Case322Extraction\nset_option maxRecDepth 24000\n'
for name,(t,u,costs) in family.items():
 w='0' if name=='core' else '';base=L.index(u)[w];X=L.index(base)['001']
 for bits in range(8):
  newbase=controls.source('a','b','c',X,[],bits);uu=(newbase,'s') if name=='core' else newbase
  for mir,tt in [(False,t),(True,A.mirror(t))]:
   n=name+str(bits)+('m' if mir else 'n');qa=L.singleton_arc(tt,'a');qb=L.singleton_arc(uu,'b');ub=L.singleton_arc(tt,'b');uc=L.singleton_arc(tt,'c')
   P=L.part(uu,'a','b');core=next(B for B in P if 'a' in B);r,C=next((p,V) for p,V in L.vertices(tt) if set(L.labels(V))==set(core))
   txt+=f'def {n}T : Tree := {ts(tt)}\ndef {n}S : Tree := {ts(uu)}\n'
   plan=f'rawPlan {n}T {n}S 0 1 2 {vs(qa)} {vs(qb)} {vs(ub)} {vs(uc)}'
   txt+=f'theorem {n}_guards : ({plan}).all (currentGuard {n}T {n}S) = true := by decide\n'
   txt+=f'theorem {n}_costs : ({plan}).map paid = ['+','.join(map(str,costs))+'] := by decide\n'
   txt+=f'theorem {n}_cover (F : List (List Nat)) (ha : agreement {n}T {n}S F = true) : ∃ child, child ∈ {plan} ∧ OriginalCover {n}T {n}S F child.partition := by\n'
   txt+=f' apply rawPlan_original_cover (X := {ts(X)}) (C := {ts(C)}) (w := {vs(w)}) (r := {vs(r)}) (sa := {str(bool(bits&1)).lower()}) (sc := {str(bool(bits&2)).lower()}) (sb := {str(bool(bits&4)).lower()})\n'
   # literal target cherry orientation from input tree
   cp,ca,cb=next((p,x,y) for p,x,y in L.cherries(tt) if {x,y}=={'a','b'})
   orientation='Or.inl' if ca=='a' else 'Or.inr'
   txt+=f' all_goals first | exact ha | exact ⟨{vs(cp)},{orientation} rfl⟩ | rfl | decide | (intro x; simp [{n}T,{n}S,leaves]; omega)\n'
# Explicit wrong current-source/edge binding, source b is true; c is false,true
(t,u,_)=A.fixtures()['ii'];txt+=f'def falseBindingT : Tree := {ts(t)}\ndef falseBindingS : Tree := {ts(u)}\n'
txt+='theorem clean_b_binding : currentGuard falseBindingT falseBindingS (bBranch falseBindingS 1 [true]) = true := by decide\n'
txt+='theorem corrupt_c_for_b_binding : currentGuard falseBindingT falseBindingS (bBranch falseBindingS 1 [false,true]) = false := by decide\n'
txt+='theorem corrupt_role_is_different : current falseBindingS falseBindingT (bBranch falseBindingS 1 [true]) ≠ current falseBindingT falseBindingS (bBranch falseBindingS 1 [true]) := by decide\n'
txt+='end Universal233.Case322Extraction.Controls\n';(D/'ExtractionControls.lean').write_text(txt)
(D/'ExtractionFalse.lean').write_text('import ExtractionControls\nopen RMAF Universal233.Rule5Case322 Universal233.Case322Extraction Universal233.Case322Extraction.Controls\nexample : currentGuard falseBindingT falseBindingS (bBranch falseBindingS 1 [false,true]) = true := by decide\nexample : (rawPlan core0nT core0nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true]).map paid = [2,1,2] := by decide\n')
print('GENERATED',len(family)*8*2,'formal fixed-pair all-F covers/guards/cost lists')
