import OneDomainV2
import OutputDefs
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentOneExchange ContactedRepair ContactedSource
namespace ContactedOneConsumer

theorem clade_filter {S U : Tree} {p : Vertex}
 (sub : CoreGraph.subtree S p=some U) (nd : (leaves S).Nodup) :
 (leaves S).filter (leaves U).contains=leaves U := by
 induction p generalizing S with
 | nil =>
  have eq : S=U := by simpa only [CoreGraph.subtree,Option.some.injEq] using sub
  subst S
  exact List.filter_eq_self.2 (fun x hx=>List.contains_iff_mem.2 hx)
 | cons side rest ih =>
  cases S with
  | leaf x => simp only [CoreGraph.subtree] at sub;cases sub
  | node l r =>
   have ns := List.nodup_append.1 nd
   cases side
   · change CoreGraph.subtree l rest=some U at sub
     have no : (leaves r).filter (leaves U).contains=[] := by
      apply List.filter_eq_nil_iff.2
      intro x hx
      have outside : x∉leaves U := fun hu=>ns.2.2 x (subtree_leaves_own sub x hu) x hx rfl
      simpa using outside
     rw [leaves,List.filter_append,ih sub ns.1,no,List.append_nil]
   · change CoreGraph.subtree r rest=some U at sub
     have no : (leaves l).filter (leaves U).contains=[] := by
      apply List.filter_eq_nil_iff.2
      intro x hx
      have outside : x∉leaves U := fun hu=>ns.2.2 x hx x (subtree_leaves_own sub x hu) rfl
      simpa using outside
     rw [leaves,List.filter_append,no,ih sub ns.2.1,List.nil_append]

theorem pendant_literal_checks {T S : Tree} {q : Vertex} {a b : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T q a b)
 (one : (cuts S a b).length=1) :
 partitionCheck (leaves S) (pendantChild S a b).partition=true ∧
 pairwiseEmbeddings S (pendantChild S a b).partition=true ∧
 (pendantChild S a b).sourceForest=OutputState.sourceForest S (pendantChild S a b).partition ∧
 (pendantChild S a b).paid+1=(pendantChild S a b).partition.length ∧
 (pendantChild S a b).paid=1 := by
 obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts proper
 have single : ∃p,cuts S a b=[p] := by
  cases h : cuts S a b with
  | nil => simp only [h,List.length_nil] at one;contradiction
  | cons p tail =>
   have zero : tail.length=0 := by
    have eq : tail.length+1=1 := by simpa only [h,List.length_cons] using one
    omega
   have eq := List.length_eq_zero_iff.1 zero
   exact ⟨p,by rw [eq]⟩
 obtain ⟨p,cut⟩ := single
 have member : p∈cuts S a b := by rw [cut];exact List.mem_cons_self
 obtain ⟨U,sub⟩ := vertex_has_subtree S p (List.mem_filter.1 member).1
 have partition := pendant_partition_one cut sub
 let X := leaves U
 let Y := (leaves S).filter (fun x=>!(leaves U).contains x)
 have xne : X≠[] := by
  obtain ⟨x,hx⟩ := ContactedRepair.leaf_witness U
  intro empty
  simp only [X,empty,List.not_mem_nil] at hx
 have aS := perm.mem_iff.1 (subtree_leaves_own ch a (by simp [leaves]))
 have outside := pendant_subtree_absent_endpoints member sub
 have ay : a∈Y := List.mem_filter.2 ⟨aS,by simpa using outside.1⟩
 have yne : Y≠[] := by intro empty;rw [empty] at ay;cases ay
 have flat : [X,Y].flatten.Perm (leaves S) := by
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
  have eq := clade_filter sub ns
  change (leaves U++(leaves S).filter (fun x=>!(leaves U).contains x)).Perm (leaves S)
  have flat := List.filter_append_perm (leaves U).contains (leaves S)
  rw [eq] at flat
  exact flat
 have part := IndependentCommon.partition_from_flatten (leaves S) [X,Y] ns
  (by intro B hb;rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hb : B=X∨B=Y) with rfl|rfl;exact xne;exact yne) flat
 have dis : disjointVertices (minimalVertices X S) (minimalVertices Y S)=true := by
  apply (disjoint_iff _ _).2
  intro v hv hy
  have noY : ∀x∈leaves U,x∉Y := by
   intro x hx hy
   have no : x∉leaves U := by simpa using (List.mem_filter.1 hy).2
   exact no hx
  exact ContactedClade.clade_span_disjoint sub ns (fun _ hx=>hx) noY v hv (minimal_in_span S Y v hy)
 have emb : pairwiseEmbeddings S [X,Y]=true := by simpa only [pairwiseEmbeddings,List.all_cons,List.all_nil,Bool.and_true] using dis
 change partitionCheck (leaves S) (pendantPartition S a b)=true ∧
  pairwiseEmbeddings S (pendantPartition S a b)=true ∧ _
 rw [partition]
 exact ⟨part,emb,rfl,by simp only [pendantChild,makeChild,cut,partition,List.length_cons,List.length_nil],one⟩

theorem selected_literal_and_coverage {T S : Tree} {reverse : Bool} {c : Candidate}
 (proper : DepthOne.proper T S=true) (selected : early T S=.one reverse c) :
 let A := (Oriented reverse T S).1
 let B := (Oriented reverse T S).2
 let child := pendantChild B c.a c.b
 partitionCheck (leaves B) child.partition=true ∧ pairwiseEmbeddings B child.partition=true ∧
 child.sourceForest=OutputState.sourceForest B child.partition ∧ child.paid+1=child.partition.length ∧
 1≤child.paid ∧
 (∀F,agreement A B F=true→∃H,feasible A B child H ∧ H.length≤F.length) := by
 obtain ⟨op,ch,actual,one⟩ := actual_one_domain proper selected
 have literal := pendant_literal_checks op ch one
 refine ⟨literal.1,literal.2.1,literal.2.2.1,literal.2.2.2.1,by rw [literal.2.2.2.2];exact Nat.le_refl _,?_⟩
 intro F hF
 obtain ⟨H,valid,bound,ref⟩ := one_pendant_exchange op ch one F hF
 exact ⟨H,⟨valid,ref⟩,bound⟩
end ContactedOneConsumer

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedOneConsumer.clade_filter
#print axioms ContactedOneConsumer.clade_filter
#check @ContactedOneConsumer.pendant_literal_checks
#print axioms ContactedOneConsumer.pendant_literal_checks
#check @ContactedOneConsumer.selected_literal_and_coverage
#print axioms ContactedOneConsumer.selected_literal_and_coverage
