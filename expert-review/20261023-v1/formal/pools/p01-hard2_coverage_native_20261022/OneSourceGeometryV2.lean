import MergeLocalityV3
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair
namespace ContactedSource

theorem coreLabels_one_eq {S U : Tree} {p : Vertex} {a b : Nat}
 (one : cuts S a b=[p]) (sub : CoreGraph.subtree S p=some U) :
 coreLabels S a b=(leaves S).filter (fun x=>!(leaves U).contains x) := by
 simp only [coreLabels,one,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
  subtree_labels_lookup sub]

theorem source_merge_one {T S U R Q : Tree} {p : Vertex} {Y : List Nat} {G : List (List Nat)} {a b z : Nat}
 (proper : DepthOne.proper T S=true) (sub : CoreGraph.subtree S p=some U)
 (Yeq : Y=(leaves S).filter (fun x=>!(leaves U).contains x))
 (rt : restrict Y T=some R) (rs : restrict Y S=some Q)
 (hcR : HasCherry a b R) (hcQ : HasCherry a b Q)
 (aY : a∈Y) (bY : b∈Y) (fresh : z∉leaves T)
 (hG : agreement T S G=true)
 (ref : VertexGeometry.Refines G [leaves U,Y])
 (singleton : [b]∈G) :
 (mergeCommon a b z G).all (restrictionAgrees T S)=true ∧
 pairwiseEmbeddings S (mergeCommon a b z G)=true := by
 have Youtside : ∀x∈Y,x∉leaves U := by
  intro x hx
  rw [Yeq] at hx
  simpa using (List.mem_filter.1 hx).2
 have sides : ∀B∈G,(∀x∈B,x∈Y)∨(∀x∈B,x∉Y) := by
  intro B hb
  obtain ⟨D,hd,bd⟩ := ref B hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl|rfl
  · exact Or.inr (fun x hx hy=>Youtside x hy (bd x hx))
  · exact Or.inl bd
 have coreAF := core_projection proper hG rt rs sides
 have coreProper := restricted_pair_proper proper Y rt rs
 have freshCore : z∉leaves R := by
  intro hz
  have lab := (restrict_labels T Y z)
  simp only [rt,optionLeaves] at lab
  exact fresh ((lab.1 hz).1)
 have singletonCore : [b]∈coreForest Y G := by
  apply List.mem_filter.2
  refine ⟨singleton,(within_iff Y [b]).2 ?_⟩
  intro x hx
  have eq : x=b := by simpa only [List.mem_singleton] using hx
  exact eq ▸ bY
 have merged := common_singleton_merge hcR hcQ coreProper freshCore _ coreAF singletonCore
 have coreLabels : ∀x∈leaves R,x∈Y := by
  intro x hx
  have lab := restrict_labels T Y x
  simp only [rt,optionLeaves] at lab
  exact (lab.1 hx).2
 have lift := core_fields_lift rt rs coreLabels merged.1
 have checks := hG
 simp only [agreement,Bool.and_eq_true] at checks
 have pInside : ∀B∈otherForest Y G,∀x∈B,x∈leaves U := by
  intro B hb
  have old := (List.mem_filter.1 hb).1
  have no : ¬within Y B=true := by simpa using (List.mem_filter.1 hb).2
  obtain ⟨D,hd,bd⟩ := ref B old
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with hx|hy
  · exact fun x hb=>hx ▸ bd x hb
  · have yes : ∀x∈B,x∈Y := fun x hb=>hy ▸ bd x hb
    exact False.elim (no ((within_iff Y B).2 yes))
 have pOutsideY : ∀B∈otherForest Y G,∀x∈B,x∉Y := fun B hb x hx hy=>Youtside x hy (pInside B hb x hx)
 have no : ∀B∈otherForest Y G,a∉B ∧ b∉B ∧ z∉B := by
  intro B hb
  refine ⟨fun ha=>pOutsideY B hb a ha aY,fun hb'=>pOutsideY B hb b hb' bY,?_⟩
  exact block_fresh fresh checks.1.1.1.1 (List.mem_filter.1 hb).1
 have nonempty : ∀B∈otherForest Y G,B≠[] := fun B hb=>partition_nonempty checks.1.1.1.1 B (List.mem_filter.1 hb).1
 have shapeP : (otherForest Y G).all (restrictionAgrees T S)=true := by
  apply List.all_eq_true.2
  intro B hb
  exact List.all_eq_true.1 checks.1.1.2 B (List.mem_filter.1 hb).1
 have hullP := pairwise_filter S G (fun B=>!within Y B) checks.2
 have after := source_fields_append sub (IndependentReconstruction.proper_parts proper).2.1 pInside
  (fun B hb x hx=>Youtside x (lift.2.2 B hb x hx)) lift.1 shapeP lift.2.1 hullP
 exact source_fields_perm (merge_core_perm a b z Y G no nonempty) after

theorem candidate_source_geometry : CandidateSourceGeometry := by
 intro T S U q p a b z F proper ch one sub hF no fresh
 obtain ⟨R,Q,rt,rs,coreProper,hcR,hcQ⟩ := shared_core_cherry_one proper ch one sub
 have Yeq := coreLabels_one_eq one sub
 have validG := original_clade_split_agreement T S U p F proper sub hF
 have ref := (original_clade_split_full proper sub hF).2.2
 have ab := core_endpoints_one one sub
 have perm := (IndependentReconstruction.proper_parts proper).2.2
 have aS := perm.mem_iff.1 (subtree_leaves_own ch a (by simp [leaves]))
 have bS := perm.mem_iff.1 (subtree_leaves_own ch b (by simp [leaves]))
 have endpoints := ab aS bS
 have refCore : VertexGeometry.Refines (splitForest (leaves U) F) [leaves U,coreLabels S a b] := by
  rw [Yeq]
  exact ref
 by_cases hb : [b]∈splitForest (leaves U) F
 · simp only [repairCandidate,hb,ite_true]
   exact source_merge_one proper sub Yeq rt rs hcR hcQ endpoints.1 endpoints.2 fresh validG refCore hb
 · have ha : [a]∈splitForest (leaves U) F := by
    rcases nonrefining_singleton proper ch one sub hF no with ha|hb'
    · exact split_keeps_singleton _ _ ha
    · exact False.elim (hb (split_keeps_singleton _ _ hb'))
   simp only [repairCandidate,hb,ite_false]
   exact source_merge_one proper sub Yeq rt rs (cherry_swap hcR) (cherry_swap hcQ)
    endpoints.2 endpoints.1 fresh validG refCore ha
end ContactedSource

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedSource.coreLabels_one_eq
#print axioms ContactedSource.coreLabels_one_eq
#check @ContactedSource.source_merge_one
#print axioms ContactedSource.source_merge_one
#check @ContactedSource.candidate_source_geometry
#print axioms ContactedSource.candidate_source_geometry
