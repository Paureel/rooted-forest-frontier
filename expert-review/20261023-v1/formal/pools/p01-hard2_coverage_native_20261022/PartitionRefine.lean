import RestrictionRefine
namespace FreshClade
open RMAF

theorem splitBlock_mem (X B C : List Nat) :
 C∈splitBlock X B ↔
  (C=B.filter X.contains ∨ C=B.filter (fun x=> !X.contains x)) ∧ C≠[] := by
 simp [splitBlock,List.isEmpty_iff]
theorem splitBlock_subset {X B C : List Nat} (h : C∈splitBlock X B) : ∀x,x∈C→x∈B := by
 rcases (splitBlock_mem X B C).mp h with ⟨h,hn⟩
 rcases h with rfl|rfl <;> exact fun x hx => (List.mem_filter.mp hx).1
theorem splitBlock_nonempty {X B C : List Nat} (h : C∈splitBlock X B) : C≠[] :=
 ((splitBlock_mem X B C).mp h).2

theorem flatten_filter_nonempty (F : List (List Nat)) :
 (F.filter (fun B=> !B.isEmpty)).flatten=F.flatten := by
 induction F with
 | nil => rfl
 | cons B F ih => cases B <;> simp_all
theorem flatten_splitBlock (X B : List Nat) :
 (splitBlock X B).flatten=B.filter X.contains ++ B.filter (fun x=> !X.contains x) := by
 unfold splitBlock
 rw [flatten_filter_nonempty]
 simp

theorem count_filter_partition (p : Nat→Bool) (B : List Nat) (x : Nat) :
 (B.filter p).count x + (B.filter (fun x=> !p x)).count x=B.count x := by
 induction B with
 | nil => simp
 | cons y B ih =>
   cases hy : p y <;> by_cases he : y=x <;> simp_all [List.filter_cons,List.count_cons] <;> omega
theorem count_splitBlock (X B : List Nat) (x : Nat) : (splitBlock X B).flatten.count x=B.count x := by
 rw [flatten_splitBlock,List.count_append]
 exact count_filter_partition X.contains B x
theorem count_splitForest (X : List Nat) (F : List (List Nat)) (x : Nat) :
 (splitForest X F).flatten.count x=F.flatten.count x := by
 induction F with
 | nil => rfl
 | cons B F ih =>
   change (splitBlock X B ++ splitForest X F).flatten.count x = (B ++ F.flatten).count x
   rw [List.flatten_append,List.count_append,List.count_append,count_splitBlock,ih]

theorem splitForest_origin {X C : List Nat} {F : List (List Nat)} (h : C∈splitForest X F) :
 ∃B, B∈F ∧ C∈splitBlock X B := by
 exact List.mem_flatMap.mp h

theorem partition_refine (X L : List Nat) (F : List (List Nat))
 (h : partitionCheck L F=true) : partitionCheck L (splitForest X F)=true := by
 simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true] at h ⊢
 rcases h with ⟨⟨hne,hcount⟩,hlab⟩
 refine ⟨⟨?_,?_⟩,?_⟩
 · intro C hC
   rcases splitForest_origin hC with ⟨B,hB,hCB⟩
   have hn := splitBlock_nonempty hCB
   simpa [List.isEmpty_iff] using hn
 · intro x hx
   simpa only [count_splitForest] using hcount x hx
 · intro x hx
   rcases List.mem_flatten.mp hx with ⟨C,hC,hx⟩
   rcases splitForest_origin hC with ⟨B,hB,hCB⟩
   exact hlab x (List.mem_flatten.mpr ⟨B,hB,splitBlock_subset hCB x hx⟩)

theorem partition_labels {L B : List Nat} {F : List (List Nat)}
 (h : partitionCheck L F=true) (hb : B∈F) : ∀x,x∈B→x∈L := by
 intro x hx
 simp only [partitionCheck,Bool.and_eq_true] at h
 have hh : F.flatten.all L.contains=true := h.2
 exact List.contains_iff_mem.mp ((List.all_eq_true.mp hh) x (List.mem_flatten.mpr ⟨B,hb,hx⟩))
end FreshClade

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshClade.splitBlock_mem
#print axioms FreshClade.splitBlock_mem
#check @FreshClade.splitBlock_subset
#print axioms FreshClade.splitBlock_subset
#check @FreshClade.splitBlock_nonempty
#print axioms FreshClade.splitBlock_nonempty
#check @FreshClade.flatten_filter_nonempty
#print axioms FreshClade.flatten_filter_nonempty
#check @FreshClade.flatten_splitBlock
#print axioms FreshClade.flatten_splitBlock
#check @FreshClade.count_filter_partition
#print axioms FreshClade.count_filter_partition
#check @FreshClade.count_splitBlock
#print axioms FreshClade.count_splitBlock
#check @FreshClade.count_splitForest
#print axioms FreshClade.count_splitForest
#check @FreshClade.splitForest_origin
#print axioms FreshClade.splitForest_origin
#check @FreshClade.partition_refine
#print axioms FreshClade.partition_refine
#check @FreshClade.partition_labels
#print axioms FreshClade.partition_labels
