import ParentsAvoid
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary ContactedHard2Parent ContactedForward ContactedHard2Overlap
namespace ContactedHard2Survival

theorem actual_competitor_scope (T S : Tree) (c d : Candidate) (p r : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d)
 (shape : c.originalCuts=[p,r]) (o : Order) (F : List (List Nat))
 (agree : agreement T S F=true) (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) :
 let A:=first o (leftParent S p) (rightParent S r) (rootParent S p r)
 let B:=second o (leftParent S p) (rightParent S r) (rootParent S p r)
 let C:=third o (leftParent S p) (rightParent S r) (rootParent S p r)
 partitionCheck (leaves S) [A,B,C]=true ∧ pairwiseEmbeddings S [A,B,C]=true ∧
 VertexGeometry.Refines F [A,B,C] ∧ (∀K,K∈F→K≠[]) ∧ pairwiseEmbeddings T F=true := by
 have perm:=original_parents_perm o (leftParent S p) (rightParent S r) (rootParent S p r)
 have checks:=ContactedHard2Parent.actual_permuted_source_checks proper selected shape _ _ _ perm
 have domain:=ContactedHard2.actual_hard2_domain proper selected
 have ref:=cohabit_refines_address proper domain.2.1.1 agree together
 rw [literal_pendant_eq,ContactedHard2Parent.actual_parent_tuple proper selected shape] at ref
 refine ⟨checks.1,checks.2,?_,agreement_nonempty T S F agree,agreement_target_embedding T S F agree⟩
 intro K kF
 obtain ⟨D,dP,sub⟩:=ref K kF
 exact ⟨D,perm.mem_iff.mp dP,sub⟩

theorem partition_parent_apart (L A B C : List Nat) (part : partitionCheck L [A,B,C]=true) :
 (∀x,x∈A→x∈B→False) ∧ (∀x,x∈A→x∈C→False) ∧ (∀x,x∈B→x∈C→False) := by
 have ne:=three_parent_ne _ _ _ _ part
 exact ⟨partition_disjoint _ _ part A B (by simp) (by simp) ne.1,
  partition_disjoint _ _ part A C (by simp) (by simp) ne.2.1,
  partition_disjoint _ _ part B C (by simp) (by simp) ne.2.2⟩

theorem actual_clique_avoidance (T S : Tree) (c d : Candidate) (p r : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d)
 (shape : c.originalCuts=[p,r]) (F : List (List Nat))
 (agree : agreement T S F=true) (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (v : RMAF.Vertex) :
 (ParentAvoids T F (rightParent S r) v ∧ ParentAvoids T F (rootParent S p r) v) ∨
 (ParentAvoids T F (leftParent S p) v ∧ ParentAvoids T F (rootParent S p r) v) ∨
 (ParentAvoids T F (leftParent S p) v ∧ ParentAvoids T F (rightParent S r) v) := by
 have scope:=actual_competitor_scope T S c d p r proper selected shape .abc F agree together
 have apart:=partition_parent_apart _ _ _ _ scope.1
 exact three_parent_avoidance _ _ _ _ _ v scope.2.2.2.1 scope.2.2.2.2 apart.1 apart.2.1 apart.2.2

theorem actual_four_avoidance (T S : Tree) (c d : Candidate) (p r : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d)
 (shape : c.originalCuts=[p,r]) (o : Order) (F : List (List Nat))
 (agree : agreement T S F=true) (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (v w : RMAF.Vertex) :
 let A:=first o (leftParent S p) (rightParent S r) (rootParent S p r)
 let B:=second o (leftParent S p) (rightParent S r) (rootParent S p r)
 let C:=third o (leftParent S p) (rightParent S r) (rootParent S p r)
 (ParentAvoids T F B v ∧ ParentAvoids T F C w) ∨
 (ParentAvoids T F B v ∧ ParentAvoids T F B w) ∨
 (ParentAvoids T F A v ∧ ParentAvoids T F C w) ∨
 (ParentAvoids T F A v ∧ ParentAvoids T F B w) := by
 have scope:=actual_competitor_scope T S c d p r proper selected shape o F agree together
 have apart:=partition_parent_apart _ _ _ _ scope.1
 exact four_parent_avoidance _ _ _ _ _ v w scope.2.2.2.1 scope.2.2.2.2 apart.1 apart.2.2
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.actual_competitor_scope
#print axioms ContactedHard2Survival.actual_competitor_scope
#check @ContactedHard2Survival.partition_parent_apart
#print axioms ContactedHard2Survival.partition_parent_apart
#check @ContactedHard2Survival.actual_clique_avoidance
#print axioms ContactedHard2Survival.actual_clique_avoidance
#check @ContactedHard2Survival.actual_four_avoidance
#print axioms ContactedHard2Survival.actual_four_avoidance
