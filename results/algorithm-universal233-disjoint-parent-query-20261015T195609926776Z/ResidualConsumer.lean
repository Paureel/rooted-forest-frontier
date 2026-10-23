import LocalCertificates
namespace OutputState
open RMAF RestrictionBridge ForestState ForestGroups VertexGeometry BinaryExchange
open Universal233 Universal233.CoreProgram Universal233.PairAssembly

/-- Conditional paid query on the WHOLE current B forest of any actual opposite
output. The supplied solver contract belongs to that exact current forest.
This is an ordinary labelled agreement reconstruction; no whole-source cut
union, solver implementation, or termination premise is silently supplied. -/
theorem every_opposite_residual_query
    (solve : Option Tree → List Tree → Nat → Option (List (List Nat)))
    (T S : Tree) (A B C D : List Nat) (aout o : Output) (q0 q : Nat)
    (FB : List (List Nat)) (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (ho : o ∈ sideOutputs S A B D q0)
    (safe : BinaryCheap.OppositeSafe S T A B C aout o)
    (goodC : restrictionAgrees S T C = true) (positive : 0 < q)
    (IH : ResidualSolverContract solve (localTarget (some T) B)
      (owned (sourceForest S o.partition) B) (q-1))
    (query : solve (localTarget (some T) B) (owned (sourceForest S o.partition) B) (q-1) = some FB) :
    let F := aout.partition ++ FB ++ [C]
    agrees (some T) (sourceForest S o.partition) F = true ∧
    agreement T S F = true ∧ RestrictionBridge.Refines F o.partition ∧
    additionalCost (sourceForest S o.partition) F =
      1 + additionalCost (owned (sourceForest S o.partition) B) FB ∧
    additionalCost (sourceForest S o.partition) F ≤ q ∧ F.length - o.partition.length ≤ q := by
  dsimp only
  obtain ⟨a,c,hra,hrc,hla,hlc,ownA,ownC,perm,proper',clear⟩ :=
    opposite_grouping T S A B C D aout o q0 hs ht same hp ho safe
  obtain ⟨hA,costA,hC,costC⟩ := opposite_local_certificates T S A B C aout o a c
    hs ht same hp safe hra hrc goodC
  have hgen : o ∈ (generate S (Assembly.taggedColor A B (fun _ => 0) (sideColor D) (fun _ => 0)) q0).outputs := ho
  obtain ⟨hQ,eQ⟩ := Assembly.generated_source_valid S _ q0 o hgen
  have hqt := (partition_labels_congr _ _ [A,B,C] same).2 hp
  have ownsA : leaves a ⊆ A := fun x hx => hla.mem_iff.1 hx
  have ownsB : ∀ s ∈ owned (sourceForest S o.partition) B, leaves s ⊆ B :=
    fun s hs => ((mem_owned _ _ _).1 hs).2
  have ownsC : ∀ s ∈ [c], leaves s ⊆ C := by
    intro s hs
    have he : s = c := by simpa using hs
    subst s
    exact fun x hx => hlc.mem_iff.1 hx
  have own := original_source_ownership S o.partition [A,B,C] hs hQ safe.1
  have proper0 := sourceForest_proper T S o.partition ht hs same hQ
  have pB : proper (localTarget (some T) B) (owned (sourceForest S o.partition) B) = true :=
    local_proper (some T) (sourceForest S o.partition) [A,B,C] proper0 hqt own B (by simp)
  obtain ⟨hB,budgetB⟩ := (IH pB).2 FB query
  obtain ⟨hgroup,exactCost⟩ := retained_A_one_plus_Bforest (some T) a
    (owned (sourceForest S o.partition) B) [c] A B C aout.partition FB [C]
    proper' hqt ownsA ownsB ownsC clear hA costA hB hC costC
  have paidLift := residual_query_lift solve (some T) a (owned (sourceForest S o.partition) B)
    [c] A B C aout.partition FB [C] q positive IH proper' hqt ownsA ownsB ownsC clear
    hA costA hC costC query
  have hstate : agrees (some T) (sourceForest S o.partition) (aout.partition ++ FB ++ [C]) = true :=
    (source_permutation _ _ _ perm _).trans hgroup
  have horiginal := (agrees_iff_original T S o.partition _ ht hs same hQ eQ).1 hstate
  have hc := cost_permutation _ _ perm (aout.partition ++ FB ++ [C])
  have hce : additionalCost (sourceForest S o.partition) (aout.partition ++ FB ++ [C]) =
      1 + additionalCost (owned (sourceForest S o.partition) B) FB := hc.trans exactCost
  refine ⟨hstate,horiginal.1,horiginal.2,hce,?_,?_⟩
  · rw [hc]
    exact paidLift.2
  · rw [←exact_additional_cost S o.partition (aout.partition ++ FB ++ [C]) hs hQ,hc]
    exact paidLift.2
end OutputState
