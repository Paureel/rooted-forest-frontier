import TaggedOutputScope
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233
namespace ContactedHard2Survival

theorem saturated_subset_perm {α : Type} (L M : List α) (nd : L.Nodup) (sub : L⊆M)
 (bound : M.length≤L.length) : L.Perm M := by
 induction L generalizing M with
 | nil=>
  have eq : M=[]:=List.eq_nil_of_length_eq_zero (by simpa only [List.length_nil] using Nat.eq_zero_of_le_zero bound)
  subst M;exact List.Perm.nil
 | cons a L ih=>
  have parts:=List.nodup_cons.mp nd
  obtain ⟨left,right,eq⟩:=List.append_of_mem (sub List.mem_cons_self)
  subst M
  have tailSub : L⊆left++right := by
   intro x hx
   have member:=sub (List.mem_cons_of_mem a hx)
   rcases List.mem_append.mp member with hl|hr
   · exact List.mem_append.mpr (Or.inl hl)
   · rcases List.mem_cons.mp hr with eq|rest
     · exact False.elim (parts.1 (eq ▸ hx))
     · exact List.mem_append.mpr (Or.inr rest)
  have tailBound : (left++right).length≤L.length := by
   simp only [List.length_append,List.length_cons] at bound ⊢
   omega
  exact (List.Perm.cons a (ih (left++right) parts.2 tailSub tailBound)).trans
   (show (left++a::right).Perm (a::(left++right)) from List.perm_middle).symm

theorem nodup_map_injective_on {α β : Type} (P : List α) (f : α→β) (nd : (P.map f).Nodup)
 (K J : α) (kP : K∈P) (jP : J∈P) (eq : f K=f J) : K=J := by
 induction P with
 | nil=>simp at kP
 | cons a P ih=>
  have parts : f a∉P.map f ∧ (P.map f).Nodup:=List.nodup_cons.mp nd
  rcases List.mem_cons.mp kP with ka|kt
  · subst K
    rcases List.mem_cons.mp jP with ja|jt
    · exact ja.symm
    · exact False.elim (parts.1 (eq.symm ▸ List.mem_map.mpr ⟨J,jt,rfl⟩))
  · rcases List.mem_cons.mp jP with ja|jt
    · subst J
      exact False.elim (parts.1 (eq ▸ List.mem_map.mpr ⟨K,kt,rfl⟩))
    · exact ih parts.2 kt jt

noncomputable def colorRepresentative (K : List Nat) : Nat := by
 classical
 exact if h:∃x,x∈K then h.choose else 0

theorem colorRepresentative_mem (K : List Nat) (nonempty : K≠[]) : colorRepresentative K∈K := by
 have he:=List.exists_mem_of_ne_nil K nonempty
 simpa only [colorRepresentative,dite_eq_left he] using he.choose_spec

theorem saturated_color_partition_unique (L : List Nat) (P : List (List Nat)) (color : Nat→Nat)
 (palette : List Nat) (nd : L.Nodup) (part : partitionCheck L P=true)
 (mono : ∀K,K∈P→LabelMonochromatic color K) (paletteND : palette.Nodup)
 (witness : ∀c,c∈palette→∃x,x∈L ∧ color x=c) (bound : P.length≤palette.length) :
 ∀K,K∈P→∀J,J∈P→∀x,x∈K→∀y,y∈J→color x=color y→K=J := by
 let blockColor:=fun K=>color (colorRepresentative K)
 have representative : ∀K,K∈P→colorRepresentative K∈K := fun K kP=>
  colorRepresentative_mem K (partition_nonempty_member L P part K kP)
 have flat:=IndependentCommon.flatten_from_partition L P nd part
 have subset : palette⊆P.map blockColor := by
  intro c hc
  obtain ⟨x,xL,xc⟩:=witness c hc
  obtain ⟨K,kP,xK⟩:=List.mem_flatten.mp (flat.mem_iff.mpr xL)
  apply List.mem_map.mpr
  exact ⟨K,kP,(mono K kP _ x (representative K kP) xK).trans xc⟩
 have perm:=saturated_subset_perm palette (P.map blockColor) paletteND subset (by simpa using bound)
 have mapND : (P.map blockColor).Nodup:=perm.nodup paletteND
 intro K kP J jP x xK y yJ same
 apply nodup_map_injective_on P blockColor mapND K J kP jP
 exact (mono K kP _ x (representative K kP) xK).trans (same.trans (mono J jP _ y (representative J jP) yJ).symm)

theorem saturated_color_refinement (L : List Nat) (P F : List (List Nat)) (color : Nat→Nat)
 (palette : List Nat) (nd : L.Nodup) (partP : partitionCheck L P=true) (partF : partitionCheck L F=true)
 (monoP : ∀K,K∈P→LabelMonochromatic color K) (monoF : ∀K,K∈F→LabelMonochromatic color K)
 (paletteND : palette.Nodup) (witness : ∀c,c∈palette→∃x,x∈L ∧ color x=c)
 (bound : P.length≤palette.length) : VertexGeometry.Refines F P := by
 have unique:=saturated_color_partition_unique L P color palette nd partP monoP paletteND witness bound
 have flat:=IndependentCommon.flatten_from_partition L P nd partP
 intro K kF
 obtain ⟨x,xK⟩:=List.exists_mem_of_ne_nil K (partition_nonempty_member L F partF K kF)
 have labels:=partition_member_labels L F partF K kF
 obtain ⟨J,jP,xJ⟩:=List.mem_flatten.mp (flat.mem_iff.mpr (labels x xK))
 refine ⟨J,jP,?_⟩
 intro y yK
 obtain ⟨U,uP,yU⟩:=List.mem_flatten.mp (flat.mem_iff.mpr (labels y yK))
 have eq:=unique J jP U uP x xJ y yU (monoF K kF x y xK yK)
 exact eq ▸ yU
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.saturated_subset_perm
#print axioms ContactedHard2Survival.saturated_subset_perm
#check @ContactedHard2Survival.nodup_map_injective_on
#print axioms ContactedHard2Survival.nodup_map_injective_on
#check @ContactedHard2Survival.colorRepresentative_mem
#print axioms ContactedHard2Survival.colorRepresentative_mem
#check @ContactedHard2Survival.saturated_color_partition_unique
#print axioms ContactedHard2Survival.saturated_color_partition_unique
#check @ContactedHard2Survival.saturated_color_refinement
#print axioms ContactedHard2Survival.saturated_color_refinement
