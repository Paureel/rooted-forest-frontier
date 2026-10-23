from pathlib import Path
p=Path(__file__).with_name('RestrictionFixtures.lean')
assert not p.exists()
s='''import FourTransitions
import MergeControls

namespace TripleDP.Transitions.Restriction.Fixtures
open TripleDP.CostRoute TripleDP.Transitions.Controls

private theorem live_leaf (A : Family (.node l r) I) (side : Bool) (i : I)
    (x : α) (ht : child l r side = .leaf x) :
    Live A side i ↔ A.support i [side] := by
  simp [Live, ht, LeafAt]

private theorem live_cherry (A : Family (.node l r) I) (side : Bool) (i : I)
    (x y : α) (ht : child l r side = .node (.leaf x) (.leaf y)) :
    Live A side i ↔ A.support i [side, false] ∨ A.support i [side, true] := by
  constructor
  · rintro ⟨a, z, hz, ha⟩
    rw [ht] at hz
    cases a with
    | nil => exact False.elim hz
    | cons b a =>
      cases b with
      | false => have he : a = [] := hz.1; subst a; exact Or.inl ha
      | true => have he : a = [] := hz.1; subst a; exact Or.inr ha
  · rintro (ha | ha)
    · exact ⟨[false], x, by rw [ht]; exact ⟨rfl, rfl⟩, ha⟩
    · exact ⟨[true], y, by rw [ht]; exact ⟨rfl, rfl⟩, ha⟩

private theorem root_charge_one (A : Family (.node l r) I) (h : OpenBranchLive A)
    (side : Bool) (i : I) (hi : A.support i [side]) :
    boundaryCharge (restrict A h side).boundary = 1 := by
  have hb := (restrict_boundary_iff A h side
    ⟨i, occupied_live A h i side ⟨[], hi⟩⟩).mpr hi
  rw [hb]
  rfl

private theorem root_charge_zero (A : Family (.node l r) I) (h : OpenBranchLive A)
    (side : Bool) (hi : ∀ i, ¬ A.support i [side]) :
    boundaryCharge (restrict A h side).boundary = 0 := by
  cases hb : (restrict A h side).boundary with
  | none => rfl
  | some i => exact False.elim (hi i.val ((restrict_boundary_iff A h side i).mp hb))

def R1 := closeBoth (singleton "a") (singleton "b")
def R2 := extendLeft (singleton "a") (singleton "b") () rfl
def R3 := extendRight (singleton "a") (singleton "b") () rfl
def R4 := merge (singleton "a") (singleton "b") () () rfl rfl
def R5 := closeBoth (merge (singleton "a") (singleton "b") () () rfl rfl) (singleton "c")
def R6 := closeBoth (closeBoth (singleton "a") (singleton "b")) (singleton "c")
def R7 := extendLeft (singleton "a") (closeBoth (singleton "b") (singleton "c")) () rfl
def R8 := merge (extendLeft (singleton "x") (singleton "x") () rfl)
  (extendRight (singleton "x") (singleton "x") () rfl) (.inl ()) (.inr ()) rfl rfl

theorem H1 : OpenBranchLive R1 := closeBoth_normal _ _
theorem H2 : OpenBranchLive R2 := extendLeft_normal _ _ _ _
theorem H3 : OpenBranchLive R3 := extendRight_normal _ _ _ _
theorem H4 : OpenBranchLive R4 := merge_normal _ _ _ _ _ _
theorem H5 : OpenBranchLive R5 := closeBoth_normal _ _
theorem H6 : OpenBranchLive R6 := closeBoth_normal _ _
theorem H7 : OpenBranchLive R7 := extendLeft_normal _ _ _ _
theorem H8 : OpenBranchLive R8 := merge_normal _ _ _ _ _ _
'''
nums=[(2,2,1,1,0,0,1,1),(2,1,1,1,0,0,1,1),(2,1,1,1,0,0,1,1),(1,0,1,1,0,0,1,1),(2,2,1,1,0,0,1,1),(3,3,2,1,2,0,0,1),(3,2,1,2,0,2,1,0),(3,2,2,2,1,1,1,1)]
children=[(('leaf','a'),('leaf','b')),(('leaf','a'),('leaf','b')),(('leaf','a'),('leaf','b')),(('leaf','a'),('leaf','b')),(('cherry','a','b'),('leaf','c')),(('cherry','a','b'),('leaf','c')),(('leaf','a'),('cherry','b','c')),(('cherry','x','x'),('cherry','x','x'))]
roots=[('.inl ()','.inr ()'),('.inl ()','.inr ()'),('.inl ()','.inr ()'),('.inl ()','.inl ()'),('.inl (.inl ())','.inr ()'),(None,'.inr ()'),('.inl ()',None),('.inl (.inl ())','.inl (.inl ())')]
unfold='closeBoth, closedSupport, liftSupport, extendLeft, extendRight, adjoinRoot, adjoinRootSupport, merge, mergeSupport, singleton, indexSum, selectIndex, selectedElems'
for k,(row,ch,rt) in enumerate(zip(nums,children,roots),1):
 n,c,nl,nr,cl,cr,bl,br=row
 for side,name,N,B,childdesc,root in zip(['false','true'],['left','right'],[nl,nr],[bl,br],ch,rt):
  helper='live_'+childdesc[0]
  args=' '.join('"'+a+'"' for a in childdesc[1:])
  s+=f'''\nprivate theorem R{k}_{name}_count : (restrict R{k} H{k} {side}).blockCount = {N} := by
  rw [restrict_count]
  have hh (i) := {helper} R{k} {side} i {args} rfl
  simp only [liveIndices, hh]
  simp [R{k}, {unfold}]

private theorem R{k}_{name}_charge : boundaryCharge (restrict R{k} H{k} {side}).boundary = {B} := by
'''
  if root is not None:
   s+=f'''  apply root_charge_one R{k} H{k} {side} ({root})
  simp [R{k}, {unfold}]
'''
  else:
   s+=f'''  apply root_charge_zero
  intro i
  cases i with
  | inl i => '''+('cases i <;> ' if k==6 else '')+f'''simp [R{k}, {unfold}]
  | inr i => '''+('cases i <;> ' if k==7 else '')+f'''simp [R{k}, {unfold}]
'''
 s+=f'''\ntheorem R{k}_numbers : R{k}.blockCount = {n} ∧ R{k}.cost = {c} ∧
    (restrict R{k} H{k} false).blockCount = {nl} ∧ (restrict R{k} H{k} true).blockCount = {nr} ∧
    (restrict R{k} H{k} false).cost = {cl} ∧ (restrict R{k} H{k} true).cost = {cr} ∧
    boundaryCharge (restrict R{k} H{k} false).boundary = {bl} ∧
    boundaryCharge (restrict R{k} H{k} true).boundary = {br} := by
  refine ⟨by decide, by decide, R{k}_left_count, R{k}_right_count, ?_, ?_, R{k}_left_charge, R{k}_right_charge⟩
  · simp only [Family.cost, R{k}_left_count, R{k}_left_charge]; decide
  · simp only [Family.cost, R{k}_right_count, R{k}_right_charge]; decide
'''
for k in range(1,9):s+=f'\n#print axioms R{k}_numbers'
s+='\nend TripleDP.Transitions.Restriction.Fixtures\n';p.write_text(s)
