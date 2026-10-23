import OneSourceGeometryV2
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair
namespace ContactedSource

def freshLabel (T : Tree) := (leaves T).foldr max 0 + 1

theorem fold_max_bound (L : List Nat) {x : Nat} (hx : x∈L) : x≤L.foldr max 0 := by
 induction L with
 | nil => cases hx
 | cons y ys ih =>
  rcases List.mem_cons.1 hx with rfl|hx
  · exact Nat.le_max_left _ _
  · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

theorem fresh_label (T : Tree) : freshLabel T∉leaves T := by
 intro member
 have le := fold_max_bound _ member
 unfold freshLabel at le
 omega

theorem candidate_full_agreement {T S U : Tree} {q p : Vertex} {a b z : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T q a b)
 (one : cuts S a b=[p]) (sub : CoreGraph.subtree S p=some U)
 {F : List (List Nat)} (hF : agreement T S F=true)
 (no : ¬VertexGeometry.Refines F (pendantPartition S a b)) (fresh : z∉leaves T) :
 agreement T S (repairCandidate a b z (leaves U) F)=true := by
 have known := candidate_known_fields proper ch one sub hF no fresh
 have source := candidate_source_geometry T S U q p a b z F proper ch one sub hF no fresh
 have self := known.1
 simp only [agreement,Bool.and_eq_true] at self ⊢
 exact ⟨⟨⟨⟨self.1.1.1.1,known.2.1⟩,source.1⟩,self.1.2⟩,source.2⟩
end ContactedSource

namespace IndependentOneExchange
/- Exact statement copied from own frozen OneExchangeOpenStatements, no instance assumed. -/
def SinglePendantRepair : Prop := ∀ (T S U : Tree) (p q : Vertex) a b F,
 DepthOne.proper T S=true → CoreGraph.CherryAt T q a b →
 cuts S a b=[p] → CoreGraph.subtree S p=some U →
 agreement T S F=true →
 ¬VertexGeometry.Refines F (pendantPartition S a b) →
 ∃H,agreement T S H=true ∧ H.length+1≤(splitForest (leaves U) F).length ∧
 VertexGeometry.Refines H (pendantPartition S a b)
end IndependentOneExchange
namespace ContactedSource

theorem single_pendant_repair : SinglePendantRepair := by
 intro T S U p q a b F proper ch one sub hF no
 let z := freshLabel T
 have fresh := fresh_label T
 have known := candidate_known_fields proper ch one sub hF no fresh
 exact ⟨repairCandidate a b z (leaves U) F,
  candidate_full_agreement proper ch one sub hF no fresh,known.2.2.2.1,known.2.2.1⟩

theorem vertex_has_subtree (S : Tree) : ∀p∈vertices S,∃U,CoreGraph.subtree S p=some U := by
 induction S with
 | leaf x =>
  intro p hp
  have eq : p=[] := by simpa only [vertices,List.mem_cons,List.not_mem_nil,or_false] using hp
  subst p
  exact ⟨.leaf x,rfl⟩
 | node l r il ir =>
  intro p hp
  rcases List.mem_cons.1 hp with rfl|hp
  · exact ⟨.node l r,rfl⟩
  · rcases List.mem_append.1 hp with hp|hp
    · obtain ⟨v,hv,eq⟩ := List.mem_map.1 hp
      subst p
      exact il v hv
    · obtain ⟨v,hv,eq⟩ := List.mem_map.1 hp
      subst p
      exact ir v hv

theorem one_pendant_exchange {T S : Tree} {q : Vertex} {a b : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T q a b)
 (one : (cuts S a b).length=1) (F : List (List Nat)) (hF : agreement T S F=true) :
 ∃H,agreement T S H=true ∧ H.length≤F.length ∧ VertexGeometry.Refines H (pendantPartition S a b) := by
 classical
 by_cases already : VertexGeometry.Refines F (pendantPartition S a b)
 · exact ⟨F,hF,Nat.le_refl _,already⟩
 · have single : ∃p,cuts S a b=[p] := by
    cases h : cuts S a b with
    | nil => simp only [h,List.length_nil] at one;contradiction
    | cons p tail =>
     have len : tail.length=0 := by
      have eq : tail.length+1=1 := by simpa only [h,List.length_cons] using one
      omega
     have empty := List.length_eq_zero_iff.1 len
     exact ⟨p,by rw [empty]⟩
   obtain ⟨p,cut⟩ := single
   have member : p∈cuts S a b := by rw [cut];exact List.mem_cons_self
   obtain ⟨U,sub⟩ := vertex_has_subtree S p (List.mem_filter.1 member).1
   obtain ⟨H,valid,bound,ref⟩ := single_pendant_repair T S U p q a b F proper ch cut sub hF already
   have split := original_split_count sub (IndependentReconstruction.proper_parts proper).2.1 hF
   exact ⟨H,valid,by omega,ref⟩

theorem one_exchange_both_orientations (T S : Tree) (reverse : Bool)
 (proper : DepthOne.proper T S=true) (q : Vertex) (a b : Nat)
 (ch : CoreGraph.CherryAt (if reverse then S else T) q a b)
 (one : (cuts (if reverse then T else S) a b).length=1)
 (F : List (List Nat)) (hF : agreement (if reverse then S else T) (if reverse then T else S) F=true) :
 ∃H,agreement (if reverse then S else T) (if reverse then T else S) H=true ∧ H.length≤F.length ∧
 VertexGeometry.Refines H (pendantPartition (if reverse then T else S) a b) := by
 have oriented : DepthOne.proper (if reverse then S else T) (if reverse then T else S)=true := by
  cases reverse
  · exact proper
  · change DepthOne.proper S T=true
    obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts proper
    simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
     And.intro ns (And.intro nt perm.symm)
 exact one_pendant_exchange oriented ch one F hF
end ContactedSource

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedSource.fold_max_bound
#print axioms ContactedSource.fold_max_bound
#check @ContactedSource.fresh_label
#print axioms ContactedSource.fresh_label
#check @ContactedSource.candidate_full_agreement
#print axioms ContactedSource.candidate_full_agreement
#check @ContactedSource.single_pendant_repair
#print axioms ContactedSource.single_pendant_repair
#check @ContactedSource.vertex_has_subtree
#print axioms ContactedSource.vertex_has_subtree
#check @ContactedSource.one_pendant_exchange
#print axioms ContactedSource.one_pendant_exchange
#check @ContactedSource.one_exchange_both_orientations
#print axioms ContactedSource.one_exchange_both_orientations
