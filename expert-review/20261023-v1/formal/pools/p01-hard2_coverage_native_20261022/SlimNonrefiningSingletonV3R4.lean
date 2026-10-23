/- Reused own frozen proof body; slim import slice, permanently CONTACTED. -/
/- Contacted repair component: a nonrefining one-cut forest isolates an endpoint. -/
import SlimSharedCoreCherryV3R4
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade
namespace ContactedRepair

theorem noncross_refines (L X : List Nat) (F : List (List Nat))
 (labels : ∀B∈F,∀x∈B,x∈L) (no : ∀B∈F,¬Crosses X B) :
 VertexGeometry.Refines F [X,L.filter (fun x=>!X.contains x)] := by
 classical
 intro B hb
 by_cases inside : ∀x∈B,x∈X
 · exact ⟨X,by simp,inside⟩
 · have outside : ∀x∈B,x∉X := by
    intro x hx hX
    apply inside
    intro y hy
    apply Classical.byContradiction
    intro yn
    exact no B hb ⟨⟨x,hx,hX⟩,⟨y,hy,yn⟩⟩
   refine ⟨L.filter (fun x=>!X.contains x),by simp,?_⟩
   intro x hx
   exact List.mem_filter.2 ⟨labels B hb x hx,by simpa using outside x hx⟩

theorem cohabit_avoids_pendant {T S U : Tree} {q p : Vertex} {a b : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T q a b)
 (cut : p∈cuts S a b) (sub : CoreGraph.subtree S p=some U)
 {F : List (List Nat)} (hF : agreement T S F=true)
 {B : List Nat} (bF : B∈F) (ha : a∈B) (hb : b∈B) : ∀x∈B,x∉leaves U := by
 have nt := (IndependentReconstruction.proper_parts proper).1
 let D := B.filter (fun x=>x != a && x != b)
 have inside : ∀x∈[a,b],x∈leaves (.node (.leaf a) (.leaf b)) := by simp [leaves]
 have outside : Absent (.node (.leaf a) (.leaf b)) D := by
  intro x hx hd
  have ne : x≠a ∧ x≠b := by simpa [D] using (List.mem_filter.1 hd).2
  simp only [leaves,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
  exact hx.elim ne.1 ne.2
 have target := clade_clean ch nt inside outside
 have reversed := agreement_swap hF
 simp only [agreement,Bool.and_eq_true] at reversed
 have shape := List.all_eq_true.1 reversed.1.1.2 B bF
 have subA : ∀x∈[a,b],x∈B := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  exact hx.elim (fun e=>e ▸ ha) (fun e=>e ▸ hb)
 have source := clean_agrees shape subA (fun _ hx=>(List.mem_filter.1 hx).1) target
 have no := clean_span_disjoint S source
 have flags := (List.mem_filter.1 cut).2
 simp only [Bool.and_eq_true] at flags
 have pn : p≠[] := by intro eq;simp [eq] at flags
 have parent : p.dropLast∈minimalVertices [a,b] S := List.contains_iff_mem.1 flags.1.2
 have absent := pendant_subtree_absent_endpoints cut sub
 intro x xB xU
 have xa : x≠a := fun eq=>absent.1 (eq ▸ xU)
 have xb : x≠b := fun eq=>absent.2 (eq ▸ xU)
 have xd : x∈D := List.mem_filter.2 ⟨xB,by simp [xa,xb]⟩
 exact no _ parent (boundary_in_span sub pn ⟨x,xU,xd⟩)

theorem cohabit_refines_one {T S U : Tree} {q p : Vertex} {a b : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T q a b)
 (one : cuts S a b=[p]) (sub : CoreGraph.subtree S p=some U)
 {F : List (List Nat)} (hF : agreement T S F=true)
 (together : ∃B∈F,a∈B ∧ b∈B) : VertexGeometry.Refines F (pendantPartition S a b) := by
 obtain ⟨B,bF,ha,hb⟩ := together
 have cut : p∈cuts S a b := by simp [one]
 have absent := cohabit_avoids_pendant proper ch cut sub hF bF ha hb
 have old := hF
 simp only [agreement,Bool.and_eq_true] at old
 have labels : ∀C∈F,∀x∈C,x∈leaves S := by
  have part := old.1.1.1.2
  simp only [partitionCheck,Bool.and_eq_true] at part
  intro C hC x hx
  exact List.contains_iff_mem.1 (List.all_eq_true.1 part.2 x (List.mem_flatten.2 ⟨C,hC,hx⟩))
 have flags := (List.mem_filter.1 cut).2
 simp only [Bool.and_eq_true] at flags
 have pp : p.dropLast∈minimalVertices [a,b] S := List.contains_iff_mem.1 flags.1.2
 have subAB : ∀x∈[a,b],x∈B := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  exact hx.elim (fun e=>e ▸ ha) (fun e=>e ▸ hb)
 have parentB := minimal_subset S subAB _ pp
 rw [pendant_partition_one one sub]
 apply noncross_refines _ _ F labels
 intro C hC cross
 obtain ⟨⟨x,xC,xU⟩,⟨y,yC,yn⟩⟩ := cross
 have parentC := crossing_boundary_in_minimal sub ⟨x,xU,xC⟩ ⟨y,labels C hC y yC,yC,yn⟩
 have eq := shared_hull_block_equal old.2 bF hC parentB parentC
 exact absent x (eq ▸ xC) xU

theorem nonrefining_singleton {T S U : Tree} {q p : Vertex} {a b : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T q a b)
 (one : cuts S a b=[p]) (sub : CoreGraph.subtree S p=some U)
 {F : List (List Nat)} (hF : agreement T S F=true)
 (no : ¬VertexGeometry.Refines F (pendantPartition S a b)) : [a]∈F ∨ [b]∈F := by
 rcases endpoint_partition_cases proper ch hF with ha|hb|together
 · exact Or.inl ha
 · exact Or.inr hb
 · exact False.elim (no (cohabit_refines_one proper ch one sub hF together))

theorem split_keeps_singleton (X : List Nat) (F : List (List Nat)) {a : Nat}
 (member : [a]∈F) : [a]∈splitForest X F := by
 apply List.mem_flatMap.2
 refine ⟨[a],member,?_⟩
 by_cases h : a∈X <;> simp [splitBlock,h]
end ContactedRepair

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedRepair.noncross_refines
#print axioms ContactedRepair.noncross_refines
#check @ContactedRepair.cohabit_avoids_pendant
#print axioms ContactedRepair.cohabit_avoids_pendant
#check @ContactedRepair.cohabit_refines_one
#print axioms ContactedRepair.cohabit_refines_one
#check @ContactedRepair.nonrefining_singleton
#print axioms ContactedRepair.nonrefining_singleton
#check @ContactedRepair.split_keeps_singleton
#print axioms ContactedRepair.split_keeps_singleton
