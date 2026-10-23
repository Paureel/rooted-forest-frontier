import DisjointLiteralBinding51
import HardConsumer
import Safety
import UnitPaidCore04
open RMAF Universal233 CherryBranching OrdinaryDispatch RestrictionBridge
set_option autoImplicit false
namespace FreshLiteralDisjoint
theorem count_one_singleton_block (a : Nat) (F : List (List Nat)) :
 List.count a F.flatten=1 → [a]∈F → ∀B,B∈F → a∈B → B=[a] := by
 induction F with
 | nil => intro count single;cases single
 | cons C F ih =>
  intro count single B hB ha
  have total : List.count a C+List.count a F.flatten=1 := by simpa using count
  have tailPositive : [a]∈F → 0<List.count a F.flatten := by
   intro hs
   exact List.count_pos_iff.mpr (List.mem_flatten.mpr ⟨[a],hs,by simp⟩)
  simp only [List.mem_cons] at single hB
  rcases single with hs | hs
  · subst C
    rcases hB with hh | ht
    · exact hh
    · have positive:=List.count_pos_iff.mpr (List.mem_flatten.mpr ⟨B,ht,ha⟩)
      simp at total
      omega
  · rcases hB with hh | ht
    · subst B
      have headPositive:=List.count_pos_iff.mpr ha
      have positive:=tailPositive hs
      omega
    · have positive:=tailPositive hs
      have tailCount : List.count a F.flatten=1 := by omega
      exact ih tailCount hs B ht ha

theorem cohabit_no_singletons (labels : List Nat) (F : List (List Nat)) (a b : Nat)
 (part : partitionCheck labels F=true) (ha : a∈labels) (hb : b∈labels)
 (different : a≠b) (cohabit : UnitPaidCombination.Cohabit a b F) : [a]∉F ∧ [b]∉F := by
 have counts : ∀x∈labels,List.count x F.flatten=1 := by
  simp only [partitionCheck,Bool.and_eq_true] at part
  intro x hx
  simpa using (List.all_eq_true.mp part.1.2) x hx
 obtain ⟨B,hB,haB,hbB⟩:=cohabit
 constructor
 · intro hsingle
   have same:=count_one_singleton_block a F (counts a ha) hsingle B hB haB
   rw [same] at hbB
   have hbEq : b=a := by simpa using hbB
   exact different hbEq.symm
 · intro hsingle
   have same:=count_one_singleton_block b F (counts b hb) hsingle B hB hbB
   rw [same] at haB
   exact different (by simpa using haB)

theorem subtree_nodup (T U : Tree) (v : Vertex) (nt : (leaves T).Nodup)
 (sub : CoreGraph.subtree T v=some U) : (leaves U).Nodup := by
 induction v generalizing T with
 | nil => change some T=some U at sub;cases sub;exact nt
 | cons b v ih =>
  cases T with
  | leaf a => change none=some U at sub;cases sub
  | node L R =>
   have both : (leaves L++leaves R).Nodup:=nt
   cases b
   · exact ih L (List.nodup_append.mp both).1 sub
   · exact ih R (List.nodup_append.mp both).2.1 sub

theorem cherry_labels_distinct {T : Tree} {v : Vertex} {a b : Nat}
 (nt : (leaves T).Nodup) (cherry : CoreGraph.CherryAt T v a b) : a≠b := by
 have nd:=subtree_nodup T (.node (.leaf a) (.leaf b)) v nt cherry
 simpa [leaves] using nd

theorem original_cohabit_refines_parents (q : Nat) (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (selected : FastOrdinary.early T S=.hard2 c d)
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (F : List (List Nat)) (agree : agreement T S F=true)
 (cohabit : UnitPaidCombination.Cohabit c.a c.b F) :
 Refines F (pendantPartition S c.a c.b) := by
 obtain ⟨nt,ns,same,pt,ps,et,es,three,fee⟩:=original_disjoint_geometry T S c d proper selected picked
 obtain ⟨ht,hs,hf,hr⟩:=original_early_hard2_fields selected
 obtain ⟨cherry,factory⟩:=selected_actual ht
 obtain ⟨p,r,horig,hdisjoint⟩:=run_disjoint_two picked
 have hcuts : cuts S c.a c.b=[p,r]:=factory.symm.trans horig
 have hnamed : HardParent.pendantOriginal S c.a c.b=[p,r]:=hcuts
 have different:=cherry_labels_distinct nt cherry
 have memA : c.a∈leaves S := (same c.a).1 (cherry_first_leaf cherry)
 have memB : c.b∈leaves S := (same c.b).1
  (subtree_leaf_mem T (.node (.leaf c.a) (.leaf c.b)) _ cherry c.b (by simp [leaves]))
 have partF : partitionCheck (leaves S) F=true := by
  have checks:=agree
  simp only [agreement,Bool.and_eq_true] at checks
  exact checks.1.1.1.2
 obtain ⟨notA,notB⟩:=cohabit_no_singletons (leaves S) F c.a c.b partF memA memB different cohabit
 have split:=PaidAssembly.hard2_refinement_split ns agree cherry hnamed
 rw [literal_parent_shape S c.a c.b p r hcuts]
 rcases split.2.2 with ha | hb | refinement
 · exact False.elim (notA ha)
 · exact False.elim (notB hb)
 · exact refinement
end FreshLiteralDisjoint
#print axioms FreshLiteralDisjoint.original_cohabit_refines_parents

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshLiteralDisjoint.count_one_singleton_block
#print axioms FreshLiteralDisjoint.count_one_singleton_block
#check @FreshLiteralDisjoint.cohabit_no_singletons
#print axioms FreshLiteralDisjoint.cohabit_no_singletons
#check @FreshLiteralDisjoint.subtree_nodup
#print axioms FreshLiteralDisjoint.subtree_nodup
#check @FreshLiteralDisjoint.cherry_labels_distinct
#print axioms FreshLiteralDisjoint.cherry_labels_distinct
#check @FreshLiteralDisjoint.original_cohabit_refines_parents
#print axioms FreshLiteralDisjoint.original_cohabit_refines_parents
