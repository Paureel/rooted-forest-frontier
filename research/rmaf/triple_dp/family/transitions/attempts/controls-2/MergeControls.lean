import MergeContract

namespace TripleDP.Transitions.Controls
open TripleDP.CostRoute

def singleton (x : α) : Family (.leaf x) Unit where
  finite := ⟨[()], by simp, by intro u; cases u; simp⟩
  support := fun _ a => a = []
  bounded := by intro _ _ h; exact h
  convex := by
    intro _ a b ha hb v hv
    subst a; subst b
    simpa [OnPath, lca] using hv.2
  labelled := by intro _; exact ⟨[], x, ⟨rfl, rfl⟩, rfl⟩
  disjoint := by intro i j _ _ _; cases i; cases j; rfl
  covers := by intro a y h; exact ⟨(), h.1⟩
  boundary := some ()
  root_spec := by intro i; cases i; simp

def T1 := merge (singleton "a") (singleton "b") () () rfl rfl

def leftAB := extendLeft (singleton "a") (singleton "b") () rfl
def T2 := merge leftAB (singleton "c") (.inl ()) () rfl rfl

def rightCD := extendRight (singleton "c") (singleton "d") () rfl
def T3 := merge leftAB rightCD (.inl ()) (.inr ()) rfl rfl

def leftABC := extendLeft
  (extendRight (singleton "a") (singleton "b") () rfl)
  (singleton "c") (.inr ()) rfl
def rightDE := extendLeft (singleton "d") (singleton "e") () rfl
def T4 := merge leftABC rightDE (.inl (.inr ())) (.inl ()) rfl rfl

def leftUnused := extendLeft (singleton "a")
  (closeBoth (singleton "b") (singleton "c")) () rfl
def T5 := merge leftUnused (singleton "d") (.inl ()) () rfl rfl

theorem T1_count : T1.blockCount = 1 := by decide
theorem T1_cost : T1.cost = 0 := by decide
theorem T1_root : T1.support (.inl ()) [] := by simp [T1, merge]
theorem T2_count : T2.blockCount = 2 := by decide
theorem T2_cost : T2.cost = 1 := by decide
theorem T2_survivor : T2.support (.inl (.inr ())) [false, true] := by
  simp [T2, merge, leftAB, extendLeft, adjoinRoot, adjoinRootSupport,
    closeBoth, closedSupport, liftSupport, singleton]
theorem T3_count : T3.blockCount = 3 := by decide
theorem T3_cost : T3.cost = 2 := by decide
theorem T3_survivors :
    T3.support (.inl (.inr ())) [false, true] ∧
    T3.support (.inr ⟨.inl (), by decide⟩) [true, false] := by
  simp [T3, merge, leftAB, rightCD, extendLeft, extendRight, adjoinRoot,
    adjoinRootSupport, closeBoth, closedSupport, liftSupport, singleton]
theorem T4_count : T4.blockCount = 4 := by decide
theorem T4_cost : T4.cost = 3 := by decide
theorem T4_stem : T4.support (.inl (.inl (.inr ()))) [false, false] := by
  simp [T4, merge, leftABC, extendLeft, adjoinRoot, adjoinRootSupport]
theorem T5_count : T5.blockCount = 3 := by decide
theorem T5_cost : T5.cost = 2 := by decide
theorem T5_unused :
    ¬ T5.support (.inl (.inl ())) [false, true] ∧
    ¬ T5.support (.inl (.inr (.inl ()))) [false, true] ∧
    ¬ T5.support (.inl (.inr (.inr ()))) [false, true] := by
  simp [T5, merge, leftUnused, extendLeft, adjoinRoot, adjoinRootSupport,
    closeBoth, closedSupport, liftSupport, singleton]

#print axioms T1_count
#print axioms T1_cost
#print axioms T1_root
#print axioms T2_count
#print axioms T2_cost
#print axioms T2_survivor
#print axioms T3_count
#print axioms T3_cost
#print axioms T3_survivors
#print axioms T4_count
#print axioms T4_cost
#print axioms T4_stem
#print axioms T5_count
#print axioms T5_cost
#print axioms T5_unused
end TripleDP.Transitions.Controls
