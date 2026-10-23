#!/usr/bin/env python3
"""Build a concrete witness using the prior generic Lean tree definitions.
The source-model definitions are reused and this is not a fresh review.
"""
from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2]
D=Path(__file__).resolve().parent
data=json.loads((R/'results/thesis-runtime-repair-history-reachable-probe.json').read_text())
names={'a':0,'c':1,'d':2,'x':3,'y':4,'W':5,'X':6,'Y':7,'h':8,'B':9,'t':10,'d0':11}
def parse(s):
 ts=re.findall(r'[(),]|[^(),\s]+',s);i=0
 def go():
  nonlocal i
  if ts[i]!='(':
   z=ts[i];i+=1;return z
  i+=1;ks=[go()]
  while ts[i]==',':i+=1;ks.append(go())
  assert ts[i]==')';i+=1
  if i<len(ts) and ts[i]=='rho':i+=1;return ('rho',ks[0])
  assert len(ks)==2
  return ('fork',*ks)
 out=go();assert i==len(ts);return out
def labels(t):
 if isinstance(t,str):return {t}
 return set().union(*(labels(c) for c in t[1:]))
def sub(t,ls):
 if labels(t)==ls and (isinstance(t,str) or t[0]!='rho'):return t
 if not isinstance(t,str):
  for c in t[1:]:
   z=sub(c,ls)
   if z is not None:return z
def lean(t):
 if isinstance(t,str):return f'(leaf {names[t]})'
 return '('+t[0]+' '+' '.join(lean(c) for c in t[1:])+')'
old=(R/'thesis_complexity/Trace.lean').read_text()
generic=old[old.index('def contains'):old.index('def U :=')]
head='''import Std
namespace HistoryTrace
inductive T where
 | leaf : Nat → T
 | fork : T → T → T
 | rho : T → T
 deriving DecidableEq, BEq, Repr
open T
-- Reused generic definitions from the original Trace.lean; this module is a
-- concrete finite witness, not a universal source-state formalization.
'''
parts=[head,generic]
for i,row in enumerate(data['rows']):
 A=parse(row['f1']);B=parse(row['f2'][0])
 assert len(row['f2'])==1
 parts += [f'def A{i} : T := {lean(A)}\n',f'def B{i} : T := {lean(B)}\n']
 P=[sub(B,set(k.split(','))) for k in row['protected2']]
 assert all(t is not None for t in P)
 parts.append(f'def P{i} : List T := ['+', '.join(lean(t) for t in P)+']\n')
for i,row in enumerate(data['rows'][1:],1):
 t=parse(row['f1'])
 def parent(t,atom):
  if isinstance(t,str):return None
  if any(c==atom for c in t[1:]):return t
  return next((z for c in t[1:] if (z:=parent(c,atom)) is not None),None)
 parts.append(f'def Top{i} : T := {lean(parent(t,"a"))}\n')
parts.append('''
def transport (prot : List T) (i : Nat) := prot.filterMap (fun s => cut s i)
def sameProtection (l r : List T) : Bool :=
 l.all (fun x => r.contains x) && r.all (fun x => l.contains x)
def legalCut (f : T) (p cuts : List T) : Bool :=
 cuts.all fun u =>
  existsSub f u && !(p.contains u) && (parentSub f u).isSome &&
  !(parentSub f u == some f && ((siblingSub f u).any fun v => p.contains v))

-- Positive and deliberately violated selection controls precede the witness.
theorem orientation_control : depth B4 3 ≥ depth B4 4 := by decide
theorem wrong_original_eligibility : eligible Top2 (3,4) = false := by decide

theorem cuts :
 cut A0 10 = some A1 ∧ cut B0 10 = some B1 ∧
 cut A1 11 = some A2 ∧ cut B1 11 = some B2 ∧
 cut A2 1 = some A3 ∧ cut B2 1 = some B3 ∧
 cut A3 2 = some A4 ∧ cut B3 2 = some B4 := by decide

theorem selected_pairs :
 selected A0 B0 A0 (0,10) = true ∧
 selected A1 B1 Top1 (0,11) = true ∧
 selected A2 B2 Top2 (0,1) = true ∧
 selected A3 B3 Top3 (0,2) = true ∧
 selected A4 B4 Top4 (3,4) = true := by decide

theorem ordered_pairs :
 depth B0 0 ≥ depth B0 10 ∧ depth B1 11 ≥ depth B1 0 ∧
 depth B2 0 ≥ depth B2 1 ∧ depth B3 2 ≥ depth B3 0 ∧
 depth B4 3 ≥ depth B4 4 := by decide

theorem pendant_counts :
 (pendants B0 0 10).length = 2 ∧ (pendants B1 11 0).length = 3 ∧
 (pendants B2 0 1).length = 2 ∧ (pendants B3 2 0).length = 2 ∧
 (pendants B4 3 4).length = 3 := by decide

theorem no_earlier_rules :
 earlier A0 B0 P0 0 10 = [false,false,false,false,false] ∧
 earlier A1 B1 P1 11 0 = [false,false,false,false,false] ∧
 earlier A2 B2 P2 0 1 = [false,false,false,false,false] ∧
 earlier A3 B3 P3 2 0 = [false,false,false,false,false] ∧
 earlier A4 B4 P4 3 4 = [false,false,false,false,false] := by decide

theorem protection_transport :
 P0 = [] ∧
 sameProtection (transport ([leaf 0] ++ pendants B0 0 10) 10) P1 = true ∧
 sameProtection (transport P1 11) P2 = true ∧
 sameProtection (transport (P2 ++ [leaf 0] ++ pendants B2 0 1) 1) P3 = true ∧
 sameProtection (transport (P3 ++ pendants B3 2 0) 2) P4 = true := by decide

theorem legal_branch_vectors :
 [legalCut B0 P0 [leaf 0], legalCut B0 P0 (pendants B0 0 10), legalCut B0 P0 [leaf 10]] = [true,true,true] ∧
 [legalCut B1 P1 [leaf 11], legalCut B1 P1 (pendants B1 11 0), legalCut B1 P1 [leaf 0]] = [true,false,false] ∧
 [legalCut B2 P2 [leaf 0], legalCut B2 P2 (pendants B2 0 1), legalCut B2 P2 [leaf 1]] = [false,false,true] ∧
 [legalCut B3 P3 (pendants B3 2 0), legalCut B3 P3 [leaf 2]] = [true,true] ∧
 [legalCut B4 P4 [leaf 3], legalCut B4 P4 (pendants B4 3 4), legalCut B4 P4 [leaf 4]] = [true,true,true] := by decide

theorem history_application_failure :
 depth A2 0 = depth A2 3 ∧ depth B2 3 > depth B2 0 ∧
 eligible Top2 (3,4) = false ∧
 ((siblingSub B4 (leaf 0)).any fun b => contains b 3) = true := by decide

-- Source annotation read separately: G1 A2 C adds a; G3 sole child resets;
-- new G1 A2 C adds a; new G3 two-child A2 endpoint branch retains a.
inductive CreditStep where | g1A2C | g3Sole | g3A2Endpoint
def credits : CreditStep → List Nat → List Nat
 | .g1A2C, _ => [0]
 | .g3Sole, _ => []
 | .g3A2Endpoint, p => p
theorem explicit_credit_schedule :
 credits .g1A2C [] = [0] ∧ credits .g3Sole [0] = [] ∧
 credits .g1A2C [] = [0] ∧ credits .g3A2Endpoint [0] = [0] := by decide

''')
thms=['orientation_control','wrong_original_eligibility','cuts','selected_pairs','ordered_pairs','pendant_counts','no_earlier_rules','protection_transport','legal_branch_vectors','history_application_failure','explicit_credit_schedule']
parts += [''.join('#print axioms '+n+'\n' for n in thms),'end HistoryTrace\n']
out=D/'HistoryTrace.lean';out.write_text(''.join(parts))
print(out)
