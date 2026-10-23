import ParentFamily
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233
open IndependentOneExchange
namespace ContactedHard2Survival

theorem split_refines_parents (D : List Nat) (F P : List (List Nat)) (ref : VertexGeometry.Refines F P) :
 VertexGeometry.Refines (splitForest D F) P := by
 intro K member
 obtain ⟨J,jF,kSplit⟩:=List.mem_flatMap.mp member
 have pieces:K∈[J.filter D.contains,J.filter (fun x=>!D.contains x)] := (List.mem_filter.mp kSplit).1
 obtain ⟨A,aP,sub⟩:=ref J jF
 refine ⟨A,aP,?_⟩
 simp only [List.mem_cons,List.not_mem_nil,or_false] at pieces
 rcases pieces with eq|eq <;>subst K
 · intro x hx;exact sub x (List.mem_filter.mp hx).1
 · intro x hx;exact sub x (List.mem_filter.mp hx).1

theorem split_side_monochrome (D : List Nat) (F : List (List Nat)) :
 ∀K,K∈splitForest D F→LabelMonochromatic (sideColor D) K := by
 intro K member
 obtain ⟨J,jF,kSplit⟩:=List.mem_flatMap.mp member
 have pieces:K∈[J.filter D.contains,J.filter (fun x=>!D.contains x)] := (List.mem_filter.mp kSplit).1
 simp only [List.mem_cons,List.not_mem_nil,or_false] at pieces
 rcases pieces with eq|eq <;>subst K
 · intro x y hx hy
   have xd : x∈D := List.contains_iff_mem.mp (List.mem_filter.mp hx).2
   have yd : y∈D := List.contains_iff_mem.mp (List.mem_filter.mp hy).2
   simp only [sideColor,ite_eq_left xd,ite_eq_left yd]
 · intro x y hx hy
   have xd : x∉D := by simpa using (List.mem_filter.mp hx).2
   have yd : y∉D := by simpa using (List.mem_filter.mp hy).2
   simp only [sideColor,ite_eq_right xd,ite_eq_right yd]

theorem side_monochrome_in_region (T : Tree) (B K : List Nat) (p : RMAF.Vertex)
 (ne : K≠[]) (sub : K⊆B) (mono : LabelMonochromatic (sideColor (PairGeometry.descendants T p)) K) :
 ∃inside : Bool,K⊆PairGeometry.sideLabels B T p inside := by
 obtain ⟨x,xK⟩:=List.exists_mem_of_ne_nil K ne
 by_cases xd : x∈PairGeometry.descendants T p
 · refine ⟨true,?_⟩
   intro y yK
   have yd : y∈PairGeometry.descendants T p := by
    apply Classical.byContradiction
    intro no
    have eq:=mono x y xK yK
    simp only [sideColor,ite_eq_left xd,ite_eq_right no] at eq
    cases eq
   apply List.mem_filter.mpr
   exact ⟨sub yK,by simpa using yd⟩
 · refine ⟨false,?_⟩
   intro y yK
   have yd : y∉PairGeometry.descendants T p := by
    intro yes
    have eq:=mono x y xK yK
    simp only [sideColor,ite_eq_right xd,ite_eq_left yes] at eq
    cases eq
   apply List.mem_filter.mpr
   exact ⟨sub yK,by simpa using yd⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.split_refines_parents
#print axioms ContactedHard2Survival.split_refines_parents
#check @ContactedHard2Survival.split_side_monochrome
#print axioms ContactedHard2Survival.split_side_monochrome
#check @ContactedHard2Survival.side_monochrome_in_region
#print axioms ContactedHard2Survival.side_monochrome_in_region
