import UnitBest02
namespace UnitPaidCombination
open RMAF ForestState GenericForest ForestGroups RestrictionBridge Universal233 Universal233.CherryBranching OrdinaryDispatch

theorem singleton_forest_witness (actual : Hard2Combine.Ordinary) (T S : Tree)
    (q x y : Nat) (proper : DepthOne.proper T S=true) (below : Below q actual)
    (xm : x∈leaves S) (ym : y∈leaves S) (xy : x≠y)
    (F : OrdinaryDispatch.Forest) (ha : agreement T S F=true)
    (budget : F.length-1≤q) (singleton : [x]∈F) :
    ∃ G,childCall (forestChild actual T) q (singletonChild S x)=some G ∧
      agreement T S G=true ∧ G.length-1≤q ∧ G.length≤F.length := by
 have guards:=proper_parts_fresh T S proper
 have same : ∀ z,z∈leaves T ↔ z∈leaves S := fun z=>guards.2.2.mem_iff
 let c:=singletonChild S x
 have part : partitionCheck (leaves S) c.partition=true :=
   singleton_partition_check guards.2.1 xm ym xy
 have emb : pairwiseEmbeddings S c.partition=true :=
   singleton_source_embeddings guards.2.1
 have mat : c.sourceForest=OutputState.sourceForest S c.partition := rfl
 have len : c.sourceForest.length=2 := by
   have raw : c.sourceForest.length=c.partition.length := by
     rw [mat]
     apply OutputState.materialized_length S c.partition
     intro U hU
     obtain ⟨s,hs,_⟩:=OutputState.checked_restrictions S c.partition guards.2.1 part U hU
     exact ⟨s,hs⟩
   simpa [c,singletonChild,makeChild,singletonPartition] using raw
 have equiv (H : OrdinaryDispatch.Forest) :
     agrees (some T) c.sourceForest H=true ↔
       agreement T S H=true ∧ VertexGeometry.Refines H c.partition := by
   rw [mat]
   exact OutputState.agrees_iff_original T S c.partition H guards.1 guards.2.1 same part emb
 have state : agrees (some T) c.sourceForest F=true :=
   (equiv F).2 ⟨ha,singleton_refinement ha singleton⟩
 have lower:=sources_le_blocks (some T) c.sourceForest F state
 have positive : 1≤q := by omega
 have strict : q-1<q := by omega
 have ih:=local_ih_below q (q-1) actual below strict
 have debit : additionalCost c.sourceForest F≤q-1 := by
   simp only [additionalCost,len]
   omega
 obtain ⟨G,found,least⟩:=ForestContinuation.forest_complete_local
   (q-1) actual ih (q-1) (Nat.le_refl _) (some T) c.sourceForest F state debit
 have sound:=GenericForest.solve_sound actual (some T) c.sourceForest (q-1) G found
 have original:=(equiv G).1 sound.1
 have glower:=sources_le_blocks (some T) c.sourceForest G sound.1
 have paid : G.length-1≤q := by
   have debitG:=sound.2
   simp only [additionalCost,len] at debitG
   omega
 refine ⟨G,?_,original.1,paid,least⟩
 simpa [childCall,remaining,c,singletonChild,makeChild,positive,forestChild] using found

theorem unit_cover_noncohabit (actual : Hard2Combine.Ordinary) (T S : Tree)
    (c : Candidate) (q : Nat) (proper : DepthOne.proper T S=true)
    (selected : Universal233.CherryBranching.select T S=some (.hard2,c))
    (below : Below q actual) (F : OrdinaryDispatch.Forest)
    (ha : agreement T S F=true) (budget : F.length-1≤q)
    (apart : ¬Cohabit c.a c.b F) :
    ∃ G,runChildren actual T S q [singletonChild S c.a,singletonChild S c.b]=some G ∧
      G.length≤F.length := by
 have cherry:=selected_cherry_fresh selected
 have guards:=proper_parts_fresh T S proper
 have labels:=cherry_guards_fresh guards.1 cherry
 have am : c.a∈leaves S:=guards.2.2.mem_iff.mp labels.1
 have bm : c.b∈leaves S:=guards.2.2.mem_iff.mp labels.2.1
 have endpoint : [c.a]∈F ∨ [c.b]∈F := by
   rcases HardParent.actual_cherry_endpoint_alternative ha cherry with first|second|together
   · exact Or.inl first
   · exact Or.inr second
   · exact False.elim (apart together)
 have witness : ∃ H,H∈childAnswers actual T q [singletonChild S c.a,singletonChild S c.b] ∧
     agreement T S H=true ∧ H.length-1≤q ∧ H.length≤F.length := by
   rcases endpoint with first|second
   · obtain ⟨H,found,hH,hbudget,least⟩:=singleton_forest_witness actual T S q c.a c.b
       proper below am bm labels.2.2 F ha budget first
     exact ⟨H,by simp [childAnswers,found],hH,hbudget,least⟩
   · obtain ⟨H,found,hH,hbudget,least⟩:=singleton_forest_witness actual T S q c.b c.a
       proper below bm am (Ne.symm labels.2.2) F ha budget second
     exact ⟨H,by simp [childAnswers,found],hH,hbudget,least⟩
 obtain ⟨H,hm,hH,hbudget,least⟩:=witness
 have valid : ordinaryAccepted T S q H=true := by simp [ordinaryAccepted,hH,hbudget]
 obtain ⟨G,found,_,leastG⟩:=best_exists_le_fresh List.length (ordinaryAccepted T S q)
   (childAnswers actual T q [singletonChild S c.a,singletonChild S c.b]) H hm valid
 exact ⟨G,found,Nat.le_trans leastG least⟩

theorem combine_query_exact (actual : Hard2Combine.Ordinary) (T S : Tree)
    (c : Candidate) (q : Nat) (paid : Universal233.BothBad.Execution)
    (proper : DepthOne.proper T S=true)
    (selected : Universal233.CherryBranching.select T S=some (.hard2,c))
    (below : Below q actual) (paidCover : CohabitingPaidCover T S c q paid) :
    QueryExact T S q (Hard2Combine.combine actual T S c.a c.b q paid).answer := by
 apply combine_of_unit_cover actual T S c q paid
 · exact run_children_sound_fresh actual T S q _
 · exact unit_cover_noncohabit actual T S c q proper selected below
 · exact paidCover
end UnitPaidCombination

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @UnitPaidCombination.singleton_forest_witness
#print axioms UnitPaidCombination.singleton_forest_witness
#check @UnitPaidCombination.unit_cover_noncohabit
#print axioms UnitPaidCombination.unit_cover_noncohabit
#check @UnitPaidCombination.combine_query_exact
#print axioms UnitPaidCombination.combine_query_exact
