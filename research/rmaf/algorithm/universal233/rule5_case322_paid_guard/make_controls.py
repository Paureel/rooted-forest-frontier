#!/usr/bin/env python3
"""Fixed exact-geometry proof controls; not a universal-case search."""
from pathlib import Path
import controls as A
D=Path(__file__).resolve().parent;L=A.L
ids={'a':0,'b':1,'c':2,'w':3,'t':4,'x':5,'p':6,'q':7,'y':8,'z':9,'s':10}
def tree(t):return '(.leaf '+str(ids[t])+')' if L.leaf(t) else '(.node '+tree(t[0])+' '+tree(t[1])+')'
def arc(p):return '['+','.join('true' if s=='1' else 'false' for s in p)+']'
def cost(xs):return '['+','.join(map(str,xs))+']'
fixtures=A.A.A.fixtures();fixtures['core']=((((('x',(('a','b'),'s')),'y'),'c'),'z'),(((('a',('x',('y','z'))),'c'),'b'),'s'),[2,1,4])
out=['import PaidCaller\nnamespace Universal233.Case322PaidGuard.Controls\nopen RMAF Universal233.CoreGraph Universal233.HardParent Universal233.CherryBranching\nopen Universal233.Rule5Local Universal233.Rule5Case322 Universal233.Case322Extraction Universal233.Case322PaidGuard\nset_option maxRecDepth 26000\n']
for name,(t,u,cs) in fixtures.items():
 X=L.index(u)['0001' if name=='core' else '001']
 for bits,mir in [(0,False),(7,True)]:
  k=name+str(bits);T=A.A.A.mirror(t) if mir else t;S=A.A.source('a','b','c',X,['s'] if name=='core' else [],bits)
  I=L.index(T);qa=L.singleton_arc(T,'a');ub=L.singleton_arc(T,'b');uc=L.singleton_arc(T,'c');w='0' if name=='core' else ''
  core=set(L.labels(T))-set(L.labels(X))-{'c'};r=next(p for p,v in L.vertices(T) if set(L.labels(v))==core);C=I[r]
  cp,ca,cb=next(q for q in L.cherries(T) if {q[1],q[2]}=={'a','b'})
  choose='Or.inl' if ca=='a' else 'Or.inr'
  front='Or.inl' if L.incident(T,L.labels(X))==[r,uc] else 'Or.inr'
  out += [f'def {k}T : Tree := {tree(T)}\ndef {k}S : Tree := {tree(S)}\n',f'def {k} : LiteralGeometry {k}T {k}S where\n',f' X := {tree(X)}\n C := {tree(C)}\n w := {arc(w)}\n r := {arc(r)}\n qa := {arc(qa)}\n ub := {arc(ub)}\n uc := {arc(uc)}\n sa := {str(bool(bits&1)).lower()}\n sc := {str(bool(bits&2)).lower()}\n sb := {str(bool(bits&4)).lower()}\n a := 0\n b := 1\n c := 2\n properT := by decide\n properS := by decide\n same := by intro x; simp [{k}T,{k}S,leaves]; omega\n source := rfl\n cherry := ⟨{arc(cp)},{choose} rfl⟩\n two := by decide\n core := rfl\n coreLabels := by intro x hx; simp [{k}T,leaves] at hx ⊢; omega\n bC := by decide\n cC := by decide\n leafA := rfl\n leafB := rfl\n leafC := rfl\n frontier := {front} (by decide)\n tailR := by decide\n tailC := by decide\n offR := by decide\n offC := by decide\n',f'theorem {k}_allGuards : ∀ child, child ∈ literalPlan {k} → currentGuard {k}T {k}S child = true := literalPlan_guards {k}\n',f'theorem {k}_costs : (guardedPlan {k}).map paid = {cost(cs)} := by decide\n',f'theorem {k}_swapGuards : ∀ child, child ∈ swappedGuardedPlan {k} → currentGuard {k}S {k}T child = true := swapped_guarded_binding {k}\n']
out+=['end Universal233.Case322PaidGuard.Controls\n']
(D/'PaidControls.lean').write_text(''.join(out))
