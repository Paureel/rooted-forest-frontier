import SelectorGuards
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233
namespace ContactedHard2Overlap

theorem partition_perm_own (L : List Nat) (F G : List (List Nat)) (nd : L.Nodup)
 (perm : F.Perm G) (part : partitionCheck L F=true) : partitionCheck L G=true := by
 have flat:=perm.flatten.symm.trans (IndependentCommon.flatten_from_partition L F nd part)
 have ne : ∀D∈G,D≠[] := fun D hd=>checked_nonempty L F part D (perm.mem_iff.2 hd)
 exact IndependentCommon.partition_from_flatten L G nd ne flat

theorem chain_guards_witness (T S : Tree) (A B C : List Nat) (v w : RMAF.Vertex)
 (part : partitionCheck (leaves S) [A,B,C]=true)
 (va : v∈minimalVertices A T) (vb : v∈minimalVertices B T)
 (wb : w∈minimalVertices B T) (wc : w∈minimalVertices C T) (clear : Clear T A C) :
 ChainGuards T A B C v w := by
 have ne:=three_parent_ne _ _ _ _ part
 have dab:=partition_disjoint _ _ part A B List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) ne.1
 have dbc:=partition_disjoint _ _ part B C (List.mem_cons_of_mem _ List.mem_cons_self)
  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) ne.2.2
 have vn:=overlap_not_target_leaf T A B v dab va vb
 have wn:=overlap_not_target_leaf T B C w dbc wb wc
 have diff : v≠w := by intro eq;have vc:=wc;rw [←eq] at vc;exact clear v va vc
 exact ⟨vn,wn,va,vb,wb,wc,clear,diff⟩

theorem chain_valid (T S : Tree) (A B C : List Nat) (o : Order) (v w : RMAF.Vertex)
 (part : partitionCheck (leaves S) [first o A B C,second o A B C,third o A B C]=true)
 (guards : ChainGuards T (first o A B C) (second o A B C) (third o A B C) v w) :
 Valid T A B C (chain T A B C o v w) := by
 have ne:=three_parent_ne _ _ _ _ part
 have apart:=partition_disjoint _ _ part _ _ List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) ne.1
 have no:=(disjoint_parent_overlap_nonlabel _ _ T v apart guards.2.2.1 guards.2.2.2.1).2
 have lower:=jointColors_at_least_two (second o A B C) T v w no guards.2.2.2.1
 by_cases two : (jointColors (second o A B C) T v w).length=2
 · simpa only [chain,if_pos two,Valid] using And.intro guards two
 · have three : 3≤(jointColors (second o A B C) T v w).length := by omega
   simpa only [chain,if_neg two,Valid] using And.intro guards three

theorem isolated_pair_pick (T : Tree) (A B C : List Nat) (o p : Order) (choice : PairGeometry.Choice)
 (h : isolated T A B C o=some (.pair p choice)) :
 PairGeometry.choose T (first o A B C) (second o A B C)=some choice ∧ o=p := by
 unfold isolated at h
 cases pick : PairGeometry.choose T (first o A B C) (second o A B C) with
 | none => simp only [pick,Option.map_none] at h;cases h
 | some ch =>
  simp only [pick,Option.map_some,Option.some.injEq,Result.pair.injEq] at h
  exact ⟨congrArg some h.2,h.1⟩

theorem select_valid (T S : Tree) (A B C : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (out : Result) (picked : select T A B C=some out) : Valid T A B C out := by
 have ndS:=(IndependentReconstruction.proper_parts proper).2.1
 cases hab : overlap T A B with
 | none =>
  cases hbc : overlap T B C with
  | none =>
   cases hac : overlap T A C with
   | none =>
    have eq : Result.disjoint=out := Option.some.inj (by simpa only [select,hab,hbc,hac] using picked)
    subst out
    have ab:= (RestrictionBridge.clear_iff _ _).2 (overlap_none_clear T A B hab)
    have bc:= (RestrictionBridge.clear_iff _ _).2 (overlap_none_clear T B C hbc)
    have ac:= (RestrictionBridge.clear_iff _ _).2 (overlap_none_clear T A C hac)
    simp only [Valid,pairwiseEmbeddings,List.all_cons,List.all_nil,ab,bc,ac,Bool.and_self]
   | some v =>
    obtain ⟨ch,found,valid⟩:=isolated_acb_complete T S A B C v proper part hab hbc hac
    have eq : Result.pair .acb ch=out := Option.some.inj (found.symm.trans picked)
    subst out
    have iso : isolated T A B C .acb=some (.pair .acb ch) := by simpa only [select,hab,hbc,hac] using found
    exact ⟨overlap_none_clear T A B hab,(RestrictionBridge.clear_symm _ _).2 (overlap_none_clear T B C hbc),
     (isolated_pair_pick T A B C .acb .acb ch iso).1,valid⟩
  | some w =>
   cases hac : overlap T A C with
   | none =>
    obtain ⟨ch,found,valid⟩:=isolated_bca_complete T S A B C w proper part hab hbc hac
    have eq : Result.pair .bca ch=out := Option.some.inj (found.symm.trans picked)
    subst out
    have iso : isolated T A B C .bca=some (.pair .bca ch) := by simpa only [select,hab,hbc,hac] using found
    exact ⟨(RestrictionBridge.clear_symm _ _).2 (overlap_none_clear T A B hab),
     (RestrictionBridge.clear_symm _ _).2 (overlap_none_clear T A C hac),
     (isolated_pair_pick T A B C .bca .bca ch iso).1,valid⟩
   | some v =>
    have eq : chain T A B C .acb v w=out := Option.some.inj (by simpa only [select,hab,hbc,hac] using picked)
    rw [←eq]
    have perm:=original_parents_perm .acb A B C
    have rotated:=partition_perm_own _ _ _ ndS perm part
    have ac:=repeated_common_some _ _ v hac
    have bc:=repeated_common_some _ _ w hbc
    exact chain_valid T S A B C .acb v w rotated
     (chain_guards_witness T S A C B v w rotated ac.1 ac.2 bc.2 bc.1 (overlap_none_clear T A B hab))
 | some v =>
  cases hbc : overlap T B C with
  | none =>
   cases hac : overlap T A C with
   | none =>
    obtain ⟨ch,found,valid⟩:=isolated_abc_complete T S A B C v proper part hab hbc hac
    have eq : Result.pair .abc ch=out := Option.some.inj (found.symm.trans picked)
    subst out
    have iso : isolated T A B C .abc=some (.pair .abc ch) := by simpa only [select,hab,hbc,hac] using found
    exact ⟨overlap_none_clear T A C hac,overlap_none_clear T B C hbc,
     (isolated_pair_pick T A B C .abc .abc ch iso).1,valid⟩
   | some w =>
    have eq : chain T A B C .bac v w=out := Option.some.inj (by simpa only [select,hab,hbc,hac] using picked)
    rw [←eq]
    have perm:=original_parents_perm .bac A B C
    have rotated:=partition_perm_own _ _ _ ndS perm part
    have ab:=repeated_common_some _ _ v hab
    have ac:=repeated_common_some _ _ w hac
    exact chain_valid T S A B C .bac v w rotated
     (chain_guards_witness T S B A C v w rotated ab.2 ab.1 ac.1 ac.2 (overlap_none_clear T B C hbc))
  | some w =>
   cases hac : overlap T A C with
   | none =>
    have eq : chain T A B C .abc v w=out := Option.some.inj (by simpa only [select,hab,hbc,hac] using picked)
    rw [←eq]
    exact chain_valid T S A B C .abc v w part (actual_chain_guards T S A B C v w part hab hbc hac)
   | some z =>
    obtain ⟨r,found,ar,br,cr⟩:=clique_search_complete T A B C v w z hab hbc hac
    have eq : Result.clique r=out := Option.some.inj (found.symm.trans picked)
    subst out
    have ne:=three_parent_ne _ _ _ _ part
    have apart:=partition_disjoint _ _ part A B List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self) ne.1
    exact ⟨overlap_not_target_leaf T A B r apart ar br,ar,br,cr⟩
end ContactedHard2Overlap

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Overlap.partition_perm_own
#print axioms ContactedHard2Overlap.partition_perm_own
#check @ContactedHard2Overlap.chain_guards_witness
#print axioms ContactedHard2Overlap.chain_guards_witness
#check @ContactedHard2Overlap.chain_valid
#print axioms ContactedHard2Overlap.chain_valid
#check @ContactedHard2Overlap.isolated_pair_pick
#print axioms ContactedHard2Overlap.isolated_pair_pick
#check @ContactedHard2Overlap.select_valid
#print axioms ContactedHard2Overlap.select_valid
