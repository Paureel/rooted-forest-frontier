import LocalExact
import Budget
import Equivalence
namespace OrdinaryDispatch
open RMAF ForestState OutputState Universal233.CherryBranching
abbrev Forest := List (List Nat)

def forestChild (actual : Tree → Tree → Nat → Option Forest)
    (T : Tree) (c : Child) (r : Nat) : Option Forest :=
  GenericForest.solve actual (some T) c.sourceForest r

/-- Only the actual residual budget is quantified. This does not assume the
ordinary callback is correct on a larger, unused budget. -/
def ExactChildAt (T S : Tree) (solver : Child → Nat → Option Forest)
    (c : Child) (r : Nat) : Prop :=
  ((∃ G, solver c r = some G) ↔ ChildWithin T S c r) ∧
  (∀ G, solver c r = some G → ExactChild T S c G ∧ G.length-c.partition.length ≤ r)

/-- Literal materialization and source geometry bind the unchanged forest
program to the exact current child. The erased completion remains in proofs. -/
theorem forest_child_exact_at
    (T S : Tree) (c : Child) (r : Nat)
    (actual : Tree → Tree → Nat → Option Forest)
    (ih : ForestMinCompletion.LocalOrdinaryIH r actual)
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup)
    (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
    (part : partitionCheck (leaves S) c.partition = true)
    (emb : pairwiseEmbeddings S c.partition = true)
    (mat : c.sourceForest = OutputState.sourceForest S c.partition) :
    ExactChildAt T S (forestChild actual T) c r := by
  have len : c.sourceForest.length = c.partition.length := by
    rw [mat]
    apply OutputState.materialized_length S c.partition
    intro U hU
    obtain ⟨s,hs,_⟩ := OutputState.checked_restrictions S c.partition ns part U hU
    exact ⟨s,hs⟩
  have equiv (F : Forest) :
      agrees (some T) c.sourceForest F = true ↔ feasible T S c F := by
    rw [mat]
    exact OutputState.agrees_iff_original T S c.partition F nt ns same part emb
  have exactness := GenericForest.LocalIH.exact_at_budget_bound r actual ih
  have sound (G : Forest) (h : forestChild actual T c r = some G) :
      feasible T S c G ∧ G.length-c.partition.length ≤ r := by
    have hs := GenericForest.solve_sound actual (some T) c.sourceForest r G h
    exact ⟨(equiv G).1 hs.1,by simpa [additionalCost,len] using hs.2⟩
  have complete (H : Forest) (hH : feasible T S c H)
      (budget : H.length-c.partition.length ≤ r) :
      ∃ G, forestChild actual T c r = some G ∧ G.length ≤ H.length := by
    apply exactness.2 (some T) c.sourceForest r H (Nat.le_refl _) ((equiv H).2 hH)
    simpa [additionalCost,len] using budget
  refine ⟨?_,?_⟩
  · constructor
    · rintro ⟨G,hG⟩
      exact ⟨G,(sound G hG).1,(sound G hG).2⟩
    · rintro ⟨H,hH,hbudget⟩
      obtain ⟨G,hG,_⟩ := complete H hH hbudget
      exact ⟨G,hG⟩
  · intro G hG
    have hs := sound G hG
    refine ⟨⟨hs.1,?_⟩,hs.2⟩
    intro H hH
    by_cases hb : H.length-c.partition.length ≤ r
    · obtain ⟨F,hF,least⟩ := complete H hH hb
      have eq : F=G := Option.some.inj (hF.symm.trans hG)
      simpa [eq] using least
    · have hg := hs.2
      omega

/-- The ordinary caller needs only the literal remaining query, not an
all-budget ExactBoundedChild premise. -/
theorem child_call_success_at
    {T S : Tree} {solver : Child → Nat → Option Forest} {c : Child} (k : Nat)
    (ih : ∀ r, remaining k c = some r → ExactChildAt T S solver c r) :
    (∃ G, childCall solver k c = some G) ↔
      ∃ r, remaining k c = some r ∧ ChildWithin T S c r := by
  cases hr : remaining k c with
  | none => simp [childCall,hr]
  | some r => simpa [childCall,hr] using (ih r hr).1
end OrdinaryDispatch
