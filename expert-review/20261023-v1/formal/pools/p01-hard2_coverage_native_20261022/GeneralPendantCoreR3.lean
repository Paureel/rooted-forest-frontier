import ForwardDomainR3
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair ContactedSource
namespace ContactedForward

theorem outside_each_cut {S : Tree} {a b : Nat} {p : Vertex} (cut : p∈cuts S a b) :
 ∀x∈coreLabels S a b,x∉subtreeLabels S p := by
 intro x hx inside
 have absent : x∉((cuts S a b).map (subtreeLabels S)).flatten := by
  simpa only [Bool.not_eq_true',←Bool.not_eq_true,List.contains_iff_mem] using (List.mem_filter.1 hx).2
 exact absent (List.mem_flatten.2 ⟨_,List.mem_map.2 ⟨p,cut,rfl⟩,inside⟩)

theorem core_endpoints_all {S : Tree} {a b : Nat} (aS : a∈leaves S) (bS : b∈leaves S) :
 a∈coreLabels S a b ∧ b∈coreLabels S a b := by
 have no (x : Nat) (endpoint : x=a∨x=b) : x∉((cuts S a b).map (subtreeLabels S)).flatten := by
  intro member
  obtain ⟨X,hX,xX⟩ := List.mem_flatten.1 member
  obtain ⟨p,cut,eq⟩ := List.mem_map.1 hX
  obtain ⟨U,sub⟩ := vertex_has_subtree S p (List.mem_filter.1 cut).1
  have absent := pendant_subtree_absent_endpoints cut sub
  have xU : x∈leaves U := by rw [←subtree_labels_lookup sub,eq];exact xX
  rcases endpoint with rfl|rfl
  · exact absent.1 xU
  · exact absent.2 xU
 constructor
 · exact List.mem_filter.2 ⟨aS,by simpa only [Bool.not_eq_true',←Bool.not_eq_true,List.contains_iff_mem] using no a (Or.inl rfl)⟩
 · exact List.mem_filter.2 ⟨bS,by simpa only [Bool.not_eq_true',←Bool.not_eq_true,List.contains_iff_mem] using no b (Or.inr rfl)⟩

theorem shared_core_all {T S : Tree} {a b : Nat} (proper : DepthOne.proper T S=true)
 (ch : HasCherry a b T) :
 ∃R Q,restrict (coreLabels S a b) T=some R ∧ restrict (coreLabels S a b) S=some Q ∧
 DepthOne.proper R Q=true ∧ HasCherry a b R ∧ HasCherry a b Q := by
 obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts proper
 have labels := IndependentCommon.syntax_labels ch
 have aS := perm.mem_iff.1 labels.1
 have bS := perm.mem_iff.1 labels.2
 have ep := core_endpoints_all aS bS
 obtain ⟨R,rt,hcR⟩ := restrict_retains_cherry ch _ ep.1 ep.2
 cases rs : restrict (coreLabels S a b) S with
 | none => exact False.elim (restrict_none_absent S _ rs a aS ep.1)
 | some Q =>
  refine ⟨R,Q,rt,rfl,restricted_pair_proper proper _ rt rs,hcR,?_⟩
  have nd : (leaves Q).Nodup := by
   have eq := restrict_leaves_eq S (coreLabels S a b)
   simp only [rs,optionLeaves] at eq
   rw [eq];exact List.Pairwise.filter _ ns
  have labs : ∀x,x∈leaves Q↔x∈leaves S ∧ x∈coreLabels S a b := by
   intro x;simpa only [rs,optionLeaves] using restrict_labels S (coreLabels S a b) x
  have subA : ∀x∈[a,b],x∈coreLabels S a b := by
   intro x hx
   rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hx : x=a∨x=b) with rfl|rfl
   · exact ep.1
   · exact ep.2
  have subD : ∀x∈coreRemainder S a b,x∈coreLabels S a b := fun x hx=>(List.mem_filter.1 hx).1
  have clean := (clean_restrict S _ [a,b] _ subA subD Q rs).1 (source_core_clean S a b)
  apply clean_two_labels_cherry Q clean nd (cherry_ne_own ch nt) ((labs a).2 ⟨aS,ep.1⟩) ((labs b).2 ⟨bS,ep.2⟩)
  intro x hx
  by_cases xa : x=a
  · exact Or.inl xa
  · by_cases xb : x=b
    · exact Or.inr (Or.inl xb)
    · exact Or.inr (Or.inr (List.mem_filter.2 ⟨((labs x).1 hx).2,by simp only [Bool.and_eq_true,bne_iff_ne];exact ⟨xa,xb⟩⟩))

theorem source_merge_all {T S : Tree} {G : List (List Nat)} {a b z : Nat}
 (proper : DepthOne.proper T S=true) (ch : HasCherry a b T) (fresh : z∉leaves T)
 (hG : agreement T S G=true) (ref : VertexGeometry.Refines G (pendantPartition S a b))
 (singleton : [b]∈G) :
 ((mergeCommon a b z G).all (restrictionAgrees T S)=true ∧ pairwiseEmbeddings S (mergeCommon a b z G)=true) ∧
 VertexGeometry.Refines (mergeCommon a b z G) (pendantPartition S a b) := by
 obtain ⟨R,Q,rt,rs,coreProper,hcR,hcQ⟩ := shared_core_all proper ch
 let Y := coreLabels S a b
 change restrict Y T=some R at rt
 change restrict Y S=some Q at rs
 have regions (B : List Nat) (hb : B∈G) :
  (∃p∈cuts S a b,∀x∈B,x∈subtreeLabels S p) ∨ (∀x∈B,x∈Y) := by
  obtain ⟨D,hd,bd⟩ := ref B hb
  rcases List.mem_append.1 hd with hp|hy
  · obtain ⟨p,cut,eq⟩ := List.mem_map.1 hp
    exact Or.inl ⟨p,cut,fun x hx=>eq ▸ bd x hx⟩
  · have eq : D=Y := by simpa only [List.mem_singleton] using hy
    exact Or.inr (fun x hx=>eq ▸ bd x hx)
 have sides : ∀B∈G,(∀x∈B,x∈Y)∨(∀x∈B,x∉Y) := by
  intro B hb
  rcases regions B hb with ⟨p,cut,inside⟩|core
  · exact Or.inr (fun x hx hy=>outside_each_cut cut x hy (inside x hx))
  · exact Or.inl core
 have coreAF := core_projection proper hG rt rs sides
 have freshCore : z∉leaves R := by
  intro hz
  have lab := restrict_labels T Y z
  simp only [rt,optionLeaves] at lab
  exact fresh ((lab.1 hz).1)
 have ep := core_endpoints_all ((IndependentReconstruction.proper_parts proper).2.2.mem_iff.1 (IndependentCommon.syntax_labels ch).1)
  ((IndependentReconstruction.proper_parts proper).2.2.mem_iff.1 (IndependentCommon.syntax_labels ch).2)
 have singletonCore : [b]∈coreForest Y G :=
  List.mem_filter.2 ⟨singleton,(within_iff Y [b]).2 (fun x hx=>(List.mem_singleton.1 hx) ▸ ep.2)⟩
 have merged := common_singleton_merge hcR hcQ coreProper freshCore _ coreAF singletonCore
 have coreLabels : ∀x∈leaves R,x∈Y := by
  intro x hx
  have lab := restrict_labels T Y x
  simp only [rt,optionLeaves] at lab
  exact (lab.1 hx).2
 have lift := core_fields_lift rt rs coreLabels merged.1
 have checks := hG
 simp only [agreement,Bool.and_eq_true] at checks
 have pInside : ∀B∈otherForest Y G,∃p∈cuts S a b,∀x∈B,x∈subtreeLabels S p := by
  intro B hb
  have no : ¬within Y B=true := by simpa only [Bool.not_eq_true',←Bool.not_eq_true] using (List.mem_filter.1 hb).2
  rcases regions B (List.mem_filter.1 hb).1 with pendant|core
  · exact pendant
  · exact False.elim (no ((within_iff Y B).2 core))
 have pOutside : ∀B∈otherForest Y G,∀x∈B,x∉Y := by
  intro B hb x hx hy
  obtain ⟨p,cut,inside⟩ := pInside B hb
  exact outside_each_cut cut x hy (inside x hx)
 have no : ∀B∈otherForest Y G,a∉B ∧ b∉B ∧ z∉B := by
  intro B hb
  exact ⟨fun ha=>pOutside B hb a ha ep.1,fun h=>pOutside B hb b h ep.2,
   block_fresh fresh checks.1.1.1.1 (List.mem_filter.1 hb).1⟩
 have nonempty : ∀B∈otherForest Y G,B≠[] := fun B hb=>partition_nonempty checks.1.1.1.1 B (List.mem_filter.1 hb).1
 have shapeP : (otherForest Y G).all (restrictionAgrees T S)=true :=
  List.all_eq_true.2 (fun B hb=>List.all_eq_true.1 checks.1.1.2 B (List.mem_filter.1 hb).1)
 have hullP := pairwise_filter S G (fun B=>!within Y B) checks.2
 have appendFields : (mergeCommon a b z (coreForest Y G)++otherForest Y G).all (restrictionAgrees T S)=true ∧
  pairwiseEmbeddings S (mergeCommon a b z (coreForest Y G)++otherForest Y G)=true := by
  constructor
  · rw [List.all_append,shapeP,Bool.and_true]
    exact lift.1
  · apply pairwise_append_own S _ _ lift.2.1 hullP
    intro A ha B hb
    obtain ⟨p,cut,inside⟩ := pInside B hb
    obtain ⟨U,sub⟩ := vertex_has_subtree S p (List.mem_filter.1 cut).1
    apply disjoint_sym
    apply (disjoint_iff _ _).2
    intro v hv hA
    apply clade_span_disjoint sub (IndependentReconstruction.proper_parts proper).2.1
     (fun x hx=>by rw [←subtree_labels_lookup sub];exact inside x hx)
     (fun x hx hxa=>outside_each_cut cut x (lift.2.2 A ha x hxa) (by rw [subtree_labels_lookup sub];exact hx)) v hv (minimal_in_span S A v hA)
 have perm := merge_core_perm a b z Y G no nonempty
 refine ⟨source_fields_perm perm appendFields,?_⟩
 intro B hb
 rcases List.mem_append.1 (perm.mem_iff.1 hb) with core|pendant
 · exact ⟨Y,List.mem_append.2 (Or.inr (List.mem_cons_self)),lift.2.2 B core⟩
 · exact ref B (List.mem_filter.1 pendant).1

end ContactedForward

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForward.outside_each_cut
#print axioms ContactedForward.outside_each_cut
#check @ContactedForward.core_endpoints_all
#print axioms ContactedForward.core_endpoints_all
#check @ContactedForward.shared_core_all
#print axioms ContactedForward.shared_core_all
#check @ContactedForward.source_merge_all
#print axioms ContactedForward.source_merge_all
