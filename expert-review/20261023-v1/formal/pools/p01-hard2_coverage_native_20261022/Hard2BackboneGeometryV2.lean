-- Universal original-forest backbone, not specialized paid hard2 coverage.
import Hard2DomainV3
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentOneExchange ContactedForward ContactedRepair ContactedSource
namespace ContactedHard2

theorem address_has_cherry {T : Tree} {p : Vertex} {a b : Nat} (ch : CoreGraph.CherryAt T p a b) : HasCherry a b T := by
 induction T generalizing p with
 | leaf x => cases p <;> simp [CoreGraph.CherryAt,CoreGraph.subtree] at ch
 | node l r il ir =>
  cases p with
  | nil =>
   have eq : Tree.node l r=Tree.node (.leaf a) (.leaf b) := Option.some.inj ch
   cases eq
   exact .here
  | cons s p => cases s with
    | false => exact .left (il ch)
    | true => exact .right (ir ch)

theorem singleton_refines_own {T S : Tree} (proper : DepthOne.proper T S=true)
 {F : List (List Nat)} (agree : agreement T S F=true) {a : Nat} (single : [a]∈F) :
 VertexGeometry.Refines F (singletonPartition S a) := by
 have check:=agree
 simp only [agreement,Bool.and_eq_true] at check
 have labels:=partition_labels check.1.1.1.2
 intro B hb
 by_cases inside : a∈B
 · have eq:=singleton_block_eq proper agree single hb inside
   exact ⟨[a],List.mem_cons_self,fun x hx=>eq ▸ hx⟩
 · refine ⟨(leaves S).filter (fun x=>x != a),List.mem_cons_of_mem _ List.mem_cons_self,?_⟩
   intro x hx
   have ne : x≠a := fun h=>inside (h ▸ hx)
   exact List.mem_filter.2 ⟨labels B hb x hx,by simpa only [bne_iff_ne] using ne⟩

theorem actual_three_child_cover {T S : Tree} {c d : Candidate}
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d)
 (F : List (List Nat)) (agree : agreement T S F=true) :
 ∃child∈branches S c.a c.b,feasible T S child F := by
 have domain:=actual_hard2_domain proper selected
 rcases endpoint_cases_all proper (address_has_cherry domain.2.1.1) agree with aF|bF|together
 · exact ⟨singletonChild S c.a,List.mem_cons_self,agree,singleton_refines_own proper agree aF⟩
 · exact ⟨singletonChild S c.b,List.mem_cons_of_mem _ List.mem_cons_self,agree,singleton_refines_own proper agree bF⟩
 · refine ⟨pendantChild S c.a c.b,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),agree,?_⟩
   have ref:=cohabit_refines_address proper domain.2.1.1 agree together
   rw [literal_pendant_eq] at ref
   exact ref

theorem singleton_source_agreement (S : Tree) (a b : Nat) (nd : (leaves S).Nodup)
 (aS : a∈leaves S) (bS : b∈leaves S) (ne : a≠b) : agreement S S (singletonPartition S a)=true := by
 obtain ⟨p,hp⟩:=leaf_address_exists_own S a aS
 have sub:=leaf_address_sound_own S a p hp
 have labels : subtreeLabels S p=[a] := by rw [subtree_labels_lookup sub];rfl
 have source : agreement S S (Rule4.literalPartition S [p])=true := by
  apply literal_source_agreement S _ nd (List.nodup_cons.2 ⟨List.not_mem_nil,.nil⟩)
  · intro v hv;rw [List.mem_singleton.1 hv];exact ⟨.leaf a,sub⟩
  · intro v hv w hw different
    exact False.elim (different ((List.mem_singleton.1 hv).trans (List.mem_singleton.1 hw).symm))
  · refine ⟨b,bS,?_⟩
    intro v hv
    rw [List.mem_singleton.1 hv,labels]
    exact fun h=>ne (List.mem_singleton.1 h).symm
 have eq : Rule4.literalPartition S [p]=singletonPartition S a := by
  simp [Rule4.literalPartition,labels,singletonPartition]
  apply List.filter_congr
  intro x hx
  by_cases eq : x=a <;> simp [eq]
 exact eq ▸ source

theorem actual_backbone_literal {T S : Tree} {c d : Candidate}
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d) :
 IndependentPaid.Literal S (branches S c.a c.b) ∧
 (∀child∈branches S c.a c.b,1≤child.paid) := by
 have dom:=actual_hard2_domain proper selected
 have parts:=IndependentReconstruction.proper_parts proper
 have ch:=address_has_cherry dom.2.1.1
 have labels:=IndependentCommon.syntax_labels ch
 have aS:=parts.2.2.mem_iff.1 labels.1
 have bS:=parts.2.2.mem_iff.1 labels.2
 have ne:=cherry_ne_own ch parts.1
 have two : (cuts S c.a c.b).length=2 := by rw [←dom.2.1.2.1];exact dom.2.1.2.2
 have sa:=singleton_source_agreement S c.a c.b parts.2.1 aS bS ne
 have sb:=singleton_source_agreement S c.b c.a parts.2.1 bS aS ne.symm
 have sp:=pendant_source_agreement S c.a c.b parts.2.1 aS
 rw [literal_pendant_eq] at sp
 have checks {P : List (List Nat)} (h : agreement S S P=true) :
   partitionCheck (leaves S) P=true ∧ pairwiseEmbeddings S P=true := by
  simp only [agreement,Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1,h.2⟩
 constructor
 · intro child member
   simp only [branches,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl
   · exact ⟨(checks sa).1,(checks sa).2,rfl,rfl⟩
   · exact ⟨(checks sb).1,(checks sb).2,rfl,rfl⟩
   · refine ⟨(checks sp).1,(checks sp).2,?_,rfl⟩
     change (cuts S c.a c.b).length+1=(pendantPartition S c.a c.b).length
     simp only [pendantPartition,List.length_append,List.length_map,List.length_cons,List.length_nil]
 · intro child member
   simp only [branches,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl
   · exact Nat.le_refl _
   · exact Nat.le_refl _
   · change 1≤(cuts S c.a c.b).length;omega
end ContactedHard2

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2.address_has_cherry
#print axioms ContactedHard2.address_has_cherry
#check @ContactedHard2.singleton_refines_own
#print axioms ContactedHard2.singleton_refines_own
#check @ContactedHard2.actual_three_child_cover
#print axioms ContactedHard2.actual_three_child_cover
#check @ContactedHard2.singleton_source_agreement
#print axioms ContactedHard2.singleton_source_agreement
#check @ContactedHard2.actual_backbone_literal
#print axioms ContactedHard2.actual_backbone_literal
