/- Contacted repair components: literal sides and the retained target-core cherry. -/
import PendantChildClosureV2
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade
namespace ContactedRepair

theorem subtree_labels_lookup {S U : Tree} {p : Vertex} (sub : CoreGraph.subtree S p=some U) :
 subtreeLabels S p=leaves U := by
 induction p generalizing S with
 | nil =>
  have eq : S=U := by simpa [CoreGraph.subtree] using sub
  subst S;rfl
 | cons side rest ih =>
  cases S with
  | leaf y => simp [CoreGraph.subtree] at sub
  | node l r => cases side <;> exact ih sub

theorem pendant_partition_one {S U : Tree} {p : Vertex} {a b : Nat}
 (one : cuts S a b=[p]) (sub : CoreGraph.subtree S p=some U) :
 pendantPartition S a b=[leaves U,(leaves S).filter (fun x=>!(leaves U).contains x)] := by
 simp [pendantPartition,coreLabels,one,subtree_labels_lookup sub]

theorem core_endpoints_one {S U : Tree} {p : Vertex} {a b : Nat}
 (one : cuts S a b=[p]) (sub : CoreGraph.subtree S p=some U)
 (aS : a∈leaves S) (bS : b∈leaves S) : a∈coreLabels S a b ∧ b∈coreLabels S a b := by
 have cut : p∈cuts S a b := by simp [one]
 have outside := pendant_subtree_absent_endpoints cut sub
 constructor
 · simp [coreLabels,one,subtree_labels_lookup sub,aS,outside.1]
 · simp [coreLabels,one,subtree_labels_lookup sub,bS,outside.2]

theorem restrict_retains_cherry {T : Tree} {a b : Nat} (hc : HasCherry a b T)
 (A : List Nat) (ha : a∈A) (hb : b∈A) :
 ∃R,restrict A T=some R ∧ HasCherry a b R := by
 induction hc with
 | here => exact ⟨_,by simp [restrict,ha,hb],.here⟩
 | swap => exact ⟨_,by simp [restrict,ha,hb],.swap⟩
 | @left l r h ih =>
  obtain ⟨L,hl,ch⟩ := ih
  cases hr : restrict A r with
  | none => exact ⟨L,by simp only [restrict,hl,hr],ch⟩
  | some R => exact ⟨.node L R,by simp only [restrict,hl,hr],.left ch⟩
 | @right l r h ih =>
  obtain ⟨R,hr,ch⟩ := ih
  cases hl : restrict A l with
  | none => exact ⟨R,by simp only [restrict,hl,hr],ch⟩
  | some L => exact ⟨.node L R,by simp only [restrict,hl,hr],.right ch⟩

theorem target_core_cherry_one {T S U : Tree} {q p : Vertex} {a b : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T q a b)
 (one : cuts S a b=[p]) (sub : CoreGraph.subtree S p=some U) :
 ∃R,restrict (coreLabels S a b) T=some R ∧ HasCherry a b R := by
 have perm := (IndependentReconstruction.proper_parts proper).2.2
 have aT := subtree_leaves_own ch a (by simp [leaves])
 have bT := subtree_leaves_own ch b (by simp [leaves])
 have ep := core_endpoints_one one sub (perm.mem_iff.1 aT) (perm.mem_iff.1 bT)
 exact restrict_retains_cherry (IndependentCommon.address_to_syntax ch) _ ep.1 ep.2

theorem split_refines_literal_pendant {T S U : Tree} {p : Vertex} {a b : Nat}
 (proper : DepthOne.proper T S=true) (one : cuts S a b=[p])
 (sub : CoreGraph.subtree S p=some U) {F : List (List Nat)} (hF : agreement T S F=true) :
 VertexGeometry.Refines (splitForest (leaves U) F) (pendantPartition S a b) := by
 rw [pendant_partition_one one sub]
 exact (original_clade_split_full proper sub hF).2.2
end ContactedRepair
