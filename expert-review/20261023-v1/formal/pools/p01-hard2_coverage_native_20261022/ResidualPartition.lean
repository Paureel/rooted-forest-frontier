import ResidualMaterialize
namespace FreshResidual
open RMAF RestrictionBridge

theorem contained_iff (B U : List Nat) : contained B U=true ↔ ∀x,x∈B→x∈U := by
 simp [contained,List.all_eq_true]

theorem family_mem (U B : List Nat) (F : List (List Nat)) :
 B∈family U F ↔ B∈F ∧ ∀x,x∈B→x∈U := by
 simp only [family,List.mem_filter,contained_iff]

theorem family_perm (U V : List Nat) (F : List (List Nat)) (hp : U.Perm V) :
 family U F=family V F := by
 have hc : (fun B=>contained B U)=(fun B=>contained B V) := by
   funext B
   apply FreshClade.bool_ext
   simp only [contained_iff]
   exact ⟨fun h x hx=>hp.mem_iff.mp (h x hx),fun h x hx=>hp.mem_iff.mpr (h x hx)⟩
 unfold family
 rw [hc]

def LabelDisjoint (B C : List Nat) : Prop := ∀x,x∈B→x∉C

theorem labelDisjoint_symm {B C : List Nat} (h : LabelDisjoint B C) : LabelDisjoint C B :=
 fun x hx hy=>h x hy hx

theorem pairwise_distinct {α : Type} {R : α→α→Prop} {F : List α}
 (sym : ∀{a b},R a b→R b a) (h : F.Pairwise R) {B C : α}
 (hb : B∈F) (hc : C∈F) (ne : B≠C) : R B C := by
 induction F with
 | nil => simp at hb
 | cons A F ih =>
   simp only [List.pairwise_cons] at h
   simp only [List.mem_cons] at hb hc
   rcases hb with rfl|hb
   · rcases hc with rfl|hc
     · exact False.elim (ne rfl)
     · exact h.1 C hc
   · rcases hc with rfl|hc
     · exact sym (h.1 B hb)
     · exact ih h.2 hb hc

theorem flatten_nodup {L : List Nat} {F : List (List Nat)}
 (hp : partitionCheck L F=true) : F.flatten.Nodup := by
 apply nodup_of_count
 intro x
 by_cases hx : x∈F.flatten
 · rcases List.mem_flatten.mp hx with ⟨B,hB,hx⟩
   have hh := partition_count hp (FreshClade.partition_labels hp hB x hx)
   omega
 · simp [List.count_eq_zero.mpr hx]

theorem labels_pairwise_aux (F : List (List Nat)) (h : F.flatten.Nodup) : F.Pairwise LabelDisjoint := by
 induction F with
 | nil => exact .nil
 | cons B F ih =>
   simp only [List.flatten_cons,List.nodup_append] at h
   refine .cons ?_ (ih h.2.1)
   intro C hC x hx hy
   exact h.2.2 x hx x (List.mem_flatten.mpr ⟨C,hC,hy⟩) rfl

theorem labels_pairwise {L : List Nat} {F : List (List Nat)}
 (hp : partitionCheck L F=true) : F.Pairwise LabelDisjoint := labels_pairwise_aux F (flatten_nodup hp)

theorem partition_blocks_nodup {L : List Nat} {F : List (List Nat)}
 (hp : partitionCheck L F=true) : F.Nodup := by
 apply (labels_pairwise hp).imp_of_mem
 intro B C hB hC hd he
 subst C
 have hn := partition_nonempty hp hB
 cases B with
 | nil => contradiction
 | cons x B => exact hd x (by simp) (by simp)

theorem partition_same {L : List Nat} {P : List (List Nat)}
 (hp : partitionCheck L P=true) {U V : List Nat} (hu : U∈P) (hv : V∈P)
 {x : Nat} (hx : x∈U) (hy : x∈V) : U=V := by
 by_cases he : U=V
 · exact he
 · exact False.elim ((pairwise_distinct labelDisjoint_symm (labels_pairwise hp) hu hv he) x hx hy)

theorem refiner_common {L : List Nat} {P F : List (List Nat)}
 (hp : partitionCheck L P=true) (ref : VertexGeometry.Refines F P)
 {U B : List Nat} (hu : U∈P) (hb : B∈F) {x : Nat} (hx : x∈U) (hy : x∈B) :
 ∀y,y∈B→y∈U := by
 rcases ref B hb with ⟨V,hv,sub⟩
 have he := partition_same hp hu hv hx (sub x hy)
 subst V
 exact sub

theorem family_count (U : List Nat) (F : List (List Nat)) (x : Nat)
 (hc : ∀B∈F,x∈B→contained B U=true) : (family U F).flatten.count x=F.flatten.count x := by
 induction F with
 | nil => rfl
 | cons B F ih =>
   have ht : ∀C∈F,x∈C→contained C U=true := fun C hC hx=>hc C (by simp [hC]) hx
   by_cases hb : contained B U=true
   · simp [family,hb,List.count_append]
     exact ih ht
   · have hn : x∉B := fun hx=>hb (hc B (by simp) hx)
     simp [family,hb,List.count_append,List.count_eq_zero.mpr hn]
     exact ih ht

theorem family_partition {L : List Nat} {P F : List (List Nat)}
 (hp : partitionCheck L P=true) (hf : partitionCheck L F=true)
 (ref : VertexGeometry.Refines F P) {U : List Nat} (hu : U∈P) :
 partitionCheck U (family U F)=true := by
 simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
 refine ⟨⟨?_,?_⟩,?_⟩
 · intro B hB
   have ne := partition_nonempty hf ((family_mem U B F).mp hB).1
   simpa [List.isEmpty_iff] using ne
 · intro x hx
   have he := family_count U F x (fun B hb hy=> (contained_iff B U).mpr (refiner_common hp ref hu hb hx hy))
   rw [he]
   exact beq_iff_eq.mpr (partition_count hf (FreshClade.partition_labels hp hu x hx))
 · intro x hx
   rcases List.mem_flatten.mp hx with ⟨B,hB,hx⟩
   exact List.contains_iff_mem.mpr (((family_mem U B F).mp hB).2 x hx)
end FreshResidual

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshResidual.contained_iff
#print axioms FreshResidual.contained_iff
#check @FreshResidual.family_mem
#print axioms FreshResidual.family_mem
#check @FreshResidual.family_perm
#print axioms FreshResidual.family_perm
#check @FreshResidual.labelDisjoint_symm
#print axioms FreshResidual.labelDisjoint_symm
#check @FreshResidual.pairwise_distinct
#print axioms FreshResidual.pairwise_distinct
#check @FreshResidual.flatten_nodup
#print axioms FreshResidual.flatten_nodup
#check @FreshResidual.labels_pairwise_aux
#print axioms FreshResidual.labels_pairwise_aux
#check @FreshResidual.labels_pairwise
#print axioms FreshResidual.labels_pairwise
#check @FreshResidual.partition_blocks_nodup
#print axioms FreshResidual.partition_blocks_nodup
#check @FreshResidual.partition_same
#print axioms FreshResidual.partition_same
#check @FreshResidual.refiner_common
#print axioms FreshResidual.refiner_common
#check @FreshResidual.family_count
#print axioms FreshResidual.family_count
#check @FreshResidual.family_partition
#print axioms FreshResidual.family_partition
