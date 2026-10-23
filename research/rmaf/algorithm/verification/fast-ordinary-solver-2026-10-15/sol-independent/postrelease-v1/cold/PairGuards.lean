import PaidConsumers
namespace Universal233.Hard2Overlap
open RMAF VertexGeometry SourceCoverage CoreProgram Integration BinaryExchange CoreGraph HardParent PaidAssembly

theorem selected_pair_guards {T S : Tree} {A B C : List Nat} {o : Order} {choice : PairGeometry.Choice}
 (ht : (leaves T).Nodup) (hl : ∀x,x∈leaves S → x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true)
 (hsource : pairwiseEmbeddings S [A,B,C]=true)
 (selected : select T A B C=some (.pair o choice)) :
 let A':=first o A B C
 let B':=second o A B C
 let C':=third o A B C
 partitionCheck (leaves S) [A',B',C']=true ∧ pairwiseEmbeddings S [A',B',C']=true ∧
 A'≠B' ∧ PairGeometry.properInput T A' B'=true ∧
 PairGeometry.choose T A' B'=some choice ∧ PairGeometry.ValidChoice T A' B' choice ∧
 (∀E,E∈[A',B',C'] → E≠A' → E≠B' → Disj T E A' ∧ Disj T E B') := by
 obtain ⟨ac,bc,hchoose,hvalid⟩ := select_sound ht hl hp selected
 have pp := permuted_partition o hp
 have pe : pairwiseEmbeddings S (parents o A B C)=true := by
  rw [FinalCutRecovery.embeddings_outer_perm S (parents_perm o A B C)]
  exact hsource
 have proper := partition_pair_proper ht hl pp
 have ab := (Assembly.parent_partition_disjoint S _ _ _ pp).1
 have ne : first o A B C≠second o A B C := by
  obtain ⟨x,hx⟩ := nonempty_witness (first o A B C) (partitionCheck_nonempty _ _ pp (first o A B C) (by simp [parents]))
  intro eq
  exact ab x hx (eq ▸ hx)
 refine ⟨pp,pe,ne,proper,hchoose,hvalid,?_⟩
 intro E mem nea neb
 simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
 rcases mem with rfl|rfl|rfl
 · exact False.elim (nea rfl)
 · exact False.elim (neb rfl)
 · exact ⟨FreshPairReview.actual_clear_disj T _ _ (clear_symm ac),FreshPairReview.actual_clear_disj T _ _ (clear_symm bc)⟩

/-- The actual first common fixture takes this completed vertex-pair call. -/
theorem actual_vertex_pair_paid {T S : Tree} {F : List (List Nat)} {o : Order} {v z p r : RMAF.Vertex} {a b q : Nat}
 (ht : (leaves T).Nodup) (hs : (leaves S).Nodup) (hl : ∀x,x∈leaves S → x∈leaves T)
 (hf : agreement T S F=true) (ch : CherryAt T z a b) (cuts : pendantOriginal S a b=[p,r])
 (selected : select T (leftParent S p) (rightParent S r) (rootParent S p r)=some (.pair o (.vertex v)))
 (hq : F.length-1≤q) (c : Rat) (base : 2≤c) :
 let A:=first o (leftParent S p) (rightParent S r) (rootParent S p r)
 let B:=second o (leftParent S p) (rightParent S r) (rootParent S p r)
 let C:=third o (leftParent S p) (rightParent S r) (rootParent S p r)
 Hard2Covered S F a b p r q (PairAssembly.vertexPairOutputs S T A B v q)
  (fun out=>PairAssembly.VertexPairClearing T out.partition A B v) ∧
 rawQMass c (PairAssembly.vertexPairOutputs S T A B v q)≤c^(-3 : Int)+c^(-4 : Int) := by
 obtain ⟨graph,hp,cases⟩ := hard2_refinement_split hs hf ch cuts
 obtain ⟨_,_,choose,valid⟩ := select_sound ht hl hp selected
 obtain ⟨av,bv,three⟩ := valid
 have pp := permuted_partition o hp
 refine ⟨⟨graph,hp,?_⟩,PairAssembly.vertex_pair_three_mass S T _ _ _ v ht hl pp av bv three q c base⟩
 rcases cases with ha|hb|hr
 · exact Or.inl ha
 · exact Or.inr (Or.inl hb)
 · have rr := refines_perm hr (parents_perm o _ _ _).symm
   obtain ⟨out,mem,hw,clear⟩ := PairAssembly.vertex_pair_cover T S _ _ _ F v q ht hs hl hf pp rr av bv hq
   exact Or.inr (Or.inr ⟨out,mem,witness_perm hw (parents_perm o _ _ _),clear⟩)
end Universal233.Hard2Overlap
