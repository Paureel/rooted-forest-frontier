/- Reviewer consumer check against an explicit ordinary partition/hull contract.
   This is an interface restatement, not a new algorithm or independent proof
   of the imported mathematics. No finite author oracle is used. -/
import FastExact
import Bridge
open RMAF
namespace IndependentReview

def LabelPartition (labels : List Nat) (F : List (List Nat)) : Prop :=
  (∀ B ∈ F, B ≠ []) ∧ (∀ x ∈ labels, F.flatten.count x = 1) ∧
  (∀ x ∈ F.flatten, x ∈ labels)

def EqualRestriction (T S : Tree) (B : List Nat) : Prop :=
  ∃ t s, restrict B T = some t ∧ restrict B S = some s ∧ RootedIso t s

def OriginalHullDisjoint (T : Tree) (F : List (List Nat)) : Prop :=
  F.Pairwise (fun A B => ∀ v,
    ¬(VertexGeometry.Hull (VertexGeometry.selectedLeaves A T) v ∧
      VertexGeometry.Hull (VertexGeometry.selectedLeaves B T) v))

def OrdinaryAF (T S : Tree) (F : List (List Nat)) : Prop :=
  LabelPartition (leaves T) F ∧ LabelPartition (leaves S) F ∧
  (∀ B ∈ F, EqualRestriction T S B) ∧ OriginalHullDisjoint T F ∧ OriginalHullDisjoint S F

theorem partition_matches (labels : List Nat) (F : List (List Nat)) :
  partitionCheck labels F = true ↔ LabelPartition labels F := by
  simp [partitionCheck,LabelPartition,List.all_eq_true,and_assoc]

theorem restrictions_match (T S : Tree) (B : List Nat) :
  restrictionAgrees T S B = true ↔ EqualRestriction T S B := by
  cases ht : restrict B T <;> cases hs : restrict B S <;>
    simp [restrictionAgrees,EqualRestriction,ht,hs,sameShape_correct]

theorem agreement_matches (T S : Tree) (F : List (List Nat)) :
  agreement T S F = true ↔ OrdinaryAF T S F := by
  simp only [agreement,Bool.and_eq_true,List.all_eq_true,partition_matches,
    restrictions_match,VertexGeometry.executable_pairwiseEmbeddings,
    OrdinaryAF,OriginalHullDisjoint,and_assoc]

def LiteralResult (T S : Tree) (k : Nat) : Option Universal233.CoreProgram.Output → Prop
  | none => ∀ F, OrdinaryAF T S F → k < F.length
  | some o => Universal233.CutRealization.RealizedOutput S o ∧ OrdinaryAF T S o.partition ∧
      o.sourceCuts.length+1=o.partition.length ∧ o.partition.length≤k ∧
      ∀ F, OrdinaryAF T S F → o.partition.length≤F.length

theorem external_contract (T S : Tree) (k : Nat)
  (uniqueT : (leaves T).Nodup) (uniqueS : (leaves S).Nodup)
  (sameLabels : (leaves T).Perm (leaves S)) :
  LiteralResult T S k (OrdinaryDispatch.FastOrdinary.external T S k) := by
  have proper := (Universal233.DepthOne.proper_iff T S).2 ⟨uniqueT,uniqueS,sameLabels⟩
  have exactness := OrdinaryDispatch.FastOrdinary.external_exact T S k proper
  cases result : OrdinaryDispatch.FastOrdinary.external T S k with
  | none =>
    simp only [result,OrdinaryDispatch.FastOrdinary.ExternalExact] at exactness
    intro F hF
    exact exactness F ((agreement_matches T S F).2 hF)
  | some o =>
    simp only [result,OrdinaryDispatch.FastOrdinary.ExternalExact] at exactness
    exact ⟨exactness.1,(agreement_matches T S o.partition).1 exactness.2.1,
      exactness.2.2.1,exactness.2.2.2.1,
      fun F hF => exactness.2.2.2.2 F ((agreement_matches T S F).2 hF)⟩

theorem zero_guard (T S : Tree) : OrdinaryDispatch.FastOrdinary.external T S 0 = none :=
  OrdinaryDispatch.FastOrdinary.external_zero T S

theorem literal_original_edges (T S : Tree) (k : Nat) (o : Universal233.CoreProgram.Output)
  (h : OrdinaryDispatch.FastOrdinary.external T S k = some o) :
  o.sourceCuts.Nodup ∧ ∀ e ∈ o.sourceCuts, Universal233.CoreGraph.Valid S e ∧ e ≠ [] :=
  OrdinaryDispatch.FastOrdinary.external_original_edges T S k h

end IndependentReview
