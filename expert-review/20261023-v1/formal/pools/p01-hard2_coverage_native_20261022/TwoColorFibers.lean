import SelectorBinding
open RMAF VertexGeometry
namespace ContactedHard2Survival

theorem projection_two_fibers (D : List Nat) (f g : Nat→Nat) (L : List (Nat×Nat))
 (count : L.length=2) (member : ∀x,x∈D→(f x,g x)∈L)
 (nf : ¬LabelMonochromatic f D) (ng : ¬LabelMonochromatic g D) :
 ∀x y,x∈D→y∈D→(f x=f y ↔ g x=g y) := by
 cases L with
 | nil=>simp at count
 | cons p rest=>
  cases rest with
  | nil=>simp at count
  | cons q rest=>
   cases rest with
   | cons r rest=>simp only [List.length_cons] at count;omega
   | nil=>
    have mem : ∀x,x∈D→(f x,g x)=p ∨ (f x,g x)=q := by
     intro x hx
     simpa only [List.mem_cons,List.not_mem_nil,or_false] using member x hx
    have fpq : p.1≠q.1 := by
     intro eq
     apply nf
     have all : ∀x,x∈D→f x=p.1 := by
      intro x hx
      rcases mem x hx with hp|hq
      · exact congrArg Prod.fst hp
      · exact (congrArg Prod.fst hq).trans eq.symm
     intro x y hx hy
     exact (all x hx).trans (all y hy).symm
    have gpq : p.2≠q.2 := by
     intro eq
     apply ng
     have all : ∀x,x∈D→g x=p.2 := by
      intro x hx
      rcases mem x hx with hp|hq
      · exact congrArg Prod.snd hp
      · exact (congrArg Prod.snd hq).trans eq.symm
     intro x y hx hy
     exact (all x hx).trans (all y hy).symm
    intro x y hx hy
    rcases mem x hx with xp|xq <;>rcases mem y hy with yp|yq
    · exact ⟨fun _=>(congrArg Prod.snd xp).trans (congrArg Prod.snd yp).symm,
       fun _=>(congrArg Prod.fst xp).trans (congrArg Prod.fst yp).symm⟩
    · exact ⟨fun eq=>False.elim (fpq ((congrArg Prod.fst xp).symm.trans (eq.trans (congrArg Prod.fst yq)))),
       fun eq=>False.elim (gpq ((congrArg Prod.snd xp).symm.trans (eq.trans (congrArg Prod.snd yq))))⟩
    · exact ⟨fun eq=>False.elim (fpq (((congrArg Prod.fst xq).symm.trans (eq.trans (congrArg Prod.fst yp))).symm)),
       fun eq=>False.elim (gpq (((congrArg Prod.snd xq).symm.trans (eq.trans (congrArg Prod.snd yp))).symm))⟩
    · exact ⟨fun _=>(congrArg Prod.snd xq).trans (congrArg Prod.snd yq).symm,
       fun _=>(congrArg Prod.fst xq).trans (congrArg Prod.fst yq).symm⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.projection_two_fibers
#print axioms ContactedHard2Survival.projection_two_fibers
