/- Pure partition refinement counting and original-objective paid identity. -/
import ReusedBest
open RMAF ForestState Universal233 Universal233.CherryBranching
namespace IndependentPaid

theorem shared_block_equal {Q : List (List Nat)} (hn : Q.flatten.Nodup)
 {U V : List Nat} (hU : U∈Q) (hV : V∈Q) {x : Nat} (xu : x∈U) (xv : x∈V) : U=V := by
 induction Q with
 | nil => simp at hU
 | cons B rest ih =>
  have parts := List.nodup_append.1 (show (B++rest.flatten).Nodup from hn)
  rcases List.mem_cons.1 hU with eU|tu
  · subst U
    rcases List.mem_cons.1 hV with eV|tv
    · exact eV.symm
    · exact False.elim (parts.2.2 x xu x (List.mem_flatten.2 ⟨V,tv,xv⟩) rfl)
  · rcases List.mem_cons.1 hV with eV|tv
    · subst V
      exact False.elim (parts.2.2 x xv x (List.mem_flatten.2 ⟨U,tu,xu⟩) rfl)
    · exact ih parts.2.1 tu tv

theorem refinement_length (L : List Nat) (F Q : List (List Nat)) (hn : L.Nodup)
 (fp : partitionCheck L F=true) (qp : partitionCheck L Q=true)
 (ref : VertexGeometry.Refines F Q) : Q.length≤F.length := by
 classical
 have qflat := (IndependentCommon.flatten_from_partition L Q hn qp).symm.nodup hn
 have nonempty : ∀B∈Q,B≠[] := by
  have check := qp
  simp only [partitionCheck,Bool.and_eq_true] at check
  intro B hB empty
  have b := List.all_eq_true.1 check.1.1 B hB
  simp [empty] at b
 have labels : ∀B∈Q,∀x∈B,x∈L := by
  have check := qp
  simp only [partitionCheck,Bool.and_eq_true] at check
  intro B hB x hx
  exact List.contains_iff_mem.1 (List.all_eq_true.1 check.2 x (List.mem_flatten.2 ⟨B,hB,hx⟩))
 have exists_pick : ∀U∈Q,∃B∈F,∃x,x∈U ∧ x∈B := by
  intro U hU
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil U (nonempty U hU)
  have covered := IndependentReconstruction.coverage L F fp (labels U hU x hx)
  obtain ⟨B,hB,hxB⟩ := List.mem_flatten.1 covered
  exact ⟨B,hB,x,hx,hxB⟩
 let pick : List Nat→List Nat := fun U=>
  if h : ∃B∈F,∃x,x∈U ∧ x∈B then Classical.choose h else []
 have spec : ∀U∈Q,pick U∈F ∧ ∃x,x∈U ∧ x∈pick U := by
  intro U hU
  have h := exists_pick U hU
  simp only [pick,dif_pos h]
  exact Classical.choose_spec h
 have inject : ∀U V,U∈Q→V∈Q→pick U=pick V→U=V := by
  intro U V hU hV eq
  obtain ⟨hB,x,hxU,hxB⟩ := spec U hU
  obtain ⟨_,y,hyV,hyB⟩ := spec V hV
  obtain ⟨W,hW,subset⟩ := ref (pick U) hB
  have ux : U=W := shared_block_equal qflat hU hW hxU (subset x hxB)
  have vx : V=W := shared_block_equal qflat hV hW hyV (subset y (eq.symm ▸ hyB))
  exact ux.trans vx.symm
 have nd : (Q.map pick).Nodup := by
  change (Q.map pick).Pairwise (fun x y=>x≠y)
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem (p:=blocks_nodup Q qflat nonempty)
  intro U V hU hV different eq
  exact different (inject U V hU hV eq)
 have sub : Q.map pick ⊆ F := by
  intro B hB
  obtain ⟨U,hU,rfl⟩ := List.mem_map.1 hB
  exact (spec U hU).1
 simpa using nd.length_le_of_subset sub

theorem paid_identity {T S : Tree} {c : Child} {F : List (List Nat)}
 (ns : (leaves S).Nodup) (part : partitionCheck (leaves S) c.partition=true)
 (paid : c.paid+1=c.partition.length) (hf : feasible T S c F) :
 c.paid+(F.length-c.partition.length)=F.length-1 := by
 have fp := hf.1
 simp only [agreement,Bool.and_eq_true] at fp
 have length := refinement_length (leaves S) F c.partition ns fp.1.1.1.2 part hf.2
 omega

theorem remaining_spec {q r : Nat} {c : Child} (h : remaining q c=some r) :
 c.paid≤q ∧ r=q-c.paid ∧ c.paid+r=q := by
 unfold remaining at h
 split at h
 · have eq := Option.some.inj h
   omega
 · contradiction

theorem remaining_strict {q r : Nat} {c : Child} (positive : 1≤c.paid)
 (h : remaining q c=some r) : r<q := by
 have spec := remaining_spec h
 omega
end IndependentPaid

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @IndependentPaid.shared_block_equal
#print axioms IndependentPaid.shared_block_equal
#check @IndependentPaid.refinement_length
#print axioms IndependentPaid.refinement_length
#check @IndependentPaid.paid_identity
#print axioms IndependentPaid.paid_identity
#check @IndependentPaid.remaining_spec
#print axioms IndependentPaid.remaining_spec
#check @IndependentPaid.remaining_strict
#print axioms IndependentPaid.remaining_strict
