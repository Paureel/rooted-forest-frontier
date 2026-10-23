import ResidualAgreement
namespace FreshResidual
open RMAF ForestState OutputState Universal233.CherryBranching

theorem refinement_length {L : List Nat} {P F : List (List Nat)}
 (hp : partitionCheck L P=true) (hf : partitionCheck L F=true)
 (ref : VertexGeometry.Refines F P) : P.length≤F.length := by
 classical
 let owner : List Nat→List Nat := fun B=>if hb:B∈F then Classical.choose (ref B hb) else []
 have op : ∀B∈F, owner B∈P ∧ ∀x,x∈B→x∈owner B := by
   intro B hb
   simp only [owner,dif_pos hb]
   exact Classical.choose_spec (ref B hb)
 have sub : P⊆F.map owner := by
   intro U hu
   have ne := partition_nonempty hp hu
   obtain ⟨x,hx⟩ : ∃x,x∈U := by
     cases U with
     | nil => contradiction
     | cons x U => exact ⟨x,by simp⟩
   have hl := FreshClade.partition_labels hp hu x hx
   have count := partition_count hf hl
   have hflat : x∈F.flatten := List.count_pos_iff.mp (by omega)
   rcases List.mem_flatten.mp hflat with ⟨B,hB,hxB⟩
   have oo := op B hB
   have he : U=owner B := partition_same hp hu oo.1 hx (oo.2 x hxB)
   exact List.mem_map.mpr ⟨B,hB,he.symm⟩
 have hh := (partition_blocks_nodup hp).length_le_of_subset sub
 simpa only [List.length_map] using hh

theorem literal_remaining {q r : Nat} {c : Child} (h : remaining q c=some r) :
 c.paid≤q ∧ q-c.paid=r := by
 by_cases hb : c.paid≤q
 · have hr : q-c.paid=r := Option.some.inj (by simpa only [remaining,if_pos hb] using h)
   exact ⟨hb,hr⟩
 · simp [remaining,hb] at h

theorem literal_additionalCost {T S : Tree} {c : Child} {F : List (List Nat)}
 (proper : Universal233.DepthOne.proper T S=true)
 (pp : partitionCheck (leaves S) c.partition=true)
 (source : c.sourceForest=sourceForest S c.partition) :
 additionalCost c.sourceForest F=F.length-c.partition.length := by
 have ns : (leaves S).Nodup := by
   simp only [Universal233.DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at proper
   exact proper.1.2
 unfold additionalCost
 rw [source,sourceForest_length ns pp]

theorem paid_residual_same_forest_iff {T S : Tree} {c : Child} {F : List (List Nat)} {q r : Nat}
 (proper : Universal233.DepthOne.proper T S=true)
 (pp : partitionCheck (leaves S) c.partition=true) (ep : pairwiseEmbeddings S c.partition=true)
 (source : c.sourceForest=sourceForest S c.partition)
 (bill : c.paid+1=c.partition.length) (rem : remaining q c=some r) :
 (feasible T S c F ∧ F.length-1≤q) ↔
 (ForestState.agrees (some T) c.sourceForest F=true ∧ additionalCost c.sourceForest F≤r) := by
 have ag := original_materialized_iff (F:=F) proper pp ep
 rw [←source] at ag
 have cost := literal_additionalCost (F:=F) proper pp source
 have rr := literal_remaining rem
 have eqv : feasible T S c F ↔ ForestState.agrees (some T) c.sourceForest F=true := by
   exact ag.symm
 have bound : feasible T S c F → (F.length-1≤q ↔ additionalCost c.sourceForest F≤r) := by
   intro hf
   have pF : partitionCheck (leaves S) F=true := by
     have a := hf.1
     simp only [agreement,Bool.and_eq_true] at a
     exact a.1.1.1.2
   have le := refinement_length pp pF hf.2
   rw [cost]
   omega
 constructor
 · rintro ⟨hf,hq⟩
   exact ⟨eqv.mp hf,(bound hf).mp hq⟩
 · rintro ⟨hf,hr⟩
   have hf' := eqv.mpr hf
   exact ⟨hf',(bound hf').mpr hr⟩

theorem paid_residual_exists_iff {T S : Tree} {c : Child} {q r : Nat}
 (proper : Universal233.DepthOne.proper T S=true)
 (pp : partitionCheck (leaves S) c.partition=true) (ep : pairwiseEmbeddings S c.partition=true)
 (source : c.sourceForest=sourceForest S c.partition)
 (bill : c.paid+1=c.partition.length) (rem : remaining q c=some r) :
 (∃F,feasible T S c F ∧ F.length-1≤q) ↔
 (∃F,ForestState.agrees (some T) c.sourceForest F=true ∧ additionalCost c.sourceForest F≤r) := by
 constructor
 · rintro ⟨F,h⟩
   exact ⟨F,(paid_residual_same_forest_iff proper pp ep source bill rem).mp h⟩
 · rintro ⟨F,h⟩
   exact ⟨F,(paid_residual_same_forest_iff proper pp ep source bill rem).mpr h⟩

theorem childWithin_materialized_iff {T S : Tree} {c : Child} {r : Nat}
 (proper : Universal233.DepthOne.proper T S=true)
 (pp : partitionCheck (leaves S) c.partition=true) (ep : pairwiseEmbeddings S c.partition=true)
 (source : c.sourceForest=sourceForest S c.partition) :
 ChildWithin T S c r ↔
 ∃F,ForestState.agrees (some T) c.sourceForest F=true ∧ additionalCost c.sourceForest F≤r := by
 have cost : ∀F,additionalCost c.sourceForest F=F.length-c.partition.length :=
   fun F=>literal_additionalCost proper pp source
 unfold ChildWithin
 constructor
 · rintro ⟨F,hf,hb⟩
   refine ⟨F,?_,?_⟩
   · rw [source]
     exact (original_materialized_iff proper pp ep).mpr hf
   · rw [cost]; exact hb
 · rintro ⟨F,hf,hb⟩
   refine ⟨F,?_,?_⟩
   · rw [source] at hf
     exact (original_materialized_iff proper pp ep).mp hf
   · rw [cost] at hb; exact hb

#print axioms paid_residual_same_forest_iff
#print axioms paid_residual_exists_iff
#print axioms childWithin_materialized_iff
end FreshResidual

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshResidual.refinement_length
#print axioms FreshResidual.refinement_length
#check @FreshResidual.literal_remaining
#print axioms FreshResidual.literal_remaining
#check @FreshResidual.literal_additionalCost
#print axioms FreshResidual.literal_additionalCost
#check @FreshResidual.paid_residual_same_forest_iff
#print axioms FreshResidual.paid_residual_same_forest_iff
#check @FreshResidual.paid_residual_exists_iff
#print axioms FreshResidual.paid_residual_exists_iff
#check @FreshResidual.childWithin_materialized_iff
#print axioms FreshResidual.childWithin_materialized_iff
