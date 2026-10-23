import CgoodCheapPlan
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem swap_three_embedding (S : Tree) (A B C : List Nat) (emb : pairwiseEmbeddings S [A,B,C]=true) :
 pairwiseEmbeddings S [B,A,C]=true := by
 have fields:=emb
 simp only [pairwiseEmbeddings,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true] at fields ⊢
 exact ⟨⟨(clear_iff _ _).mpr ((clear_symm _ _).mp ((clear_iff _ _).mp fields.1.1)),fields.2⟩,fields.1.2⟩

theorem bothbad_budget_four (T S : Tree) (A B C : List Nat) (q : Nat) (F : List (List Nat))
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) [A,B,C]=true)
 (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C]) (budget : F.length-1≤q)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false) : 4≤q := by
 have twoA:=bad_parent_family_two T S [A,B,C] F A proper parents agree ref (by simp) badA
 have twoB:=bad_parent_family_two T S [A,B,C] F B proper parents agree ref (by simp) badB
 have oneC:=checked_parent_family_positive (leaves S) [A,B,C] F C parents (agreement_source_partition T S F agree) ref (by simp)
 have total:=(three_family_perm A B C F (partition_parent_apart _ _ _ _ parents) ref (agreement_nonempty T S F agree)).length_eq
 simp only [List.length_append] at total
 omega

theorem cgood_plan_coverage (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (A B C : List Nat) (e : RMAF.Vertex×RMAF.Vertex) (F : List (List Nat))
 (below : PaidInstances.BelowBudget ordinary q)
 (contract : ParentExecutionContract (GenericForest.solve (PaidInstances.OwnPaid ordinary q)) q)
 (proper : DepthOne.proper T S=true) (parents : partitionCheck (leaves S) [A,B,C]=true)
 (swapped : partitionCheck (leaves S) [B,A,C]=true) (sourceEmb : pairwiseEmbeddings S [A,B,C]=true)
 (edge : e∈PairGeometry.edges T) (clearAB : PairGeometry.ActualClear T A B e.2)
 (clearAC : Clear (minimalVertices A T) (minimalVertices C T))
 (clearBC : Clear (minimalVertices B T) (minimalVertices C T))
 (xa ya xb yb : Nat) (xaA : xa∈A) (yaA : ya∈A) (xbB : xb∈B) (ybB : yb∈B)
 (xaD : xa∈PairGeometry.descendants T e.2) (yaN : ya∉PairGeometry.descendants T e.2)
 (xbD : xb∈PairGeometry.descendants T e.2) (ybN : yb∉PairGeometry.descendants T e.2)
 (badA : restrictionAgrees S T A=false) (badB : restrictionAgrees S T B=false) (goodC : restrictionAgrees S T C=true)
 (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C]) (budget : F.length-1≤q) :
 ∃G,(BothBad.solvePair (GenericForest.solve (PaidInstances.OwnPaid ordinary q)) S T A B C e q).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 let D:=PairGeometry.descendants T e.2
 let a:=(generate S (edgeCheapColor A B D) 3).outputs
 let b:=(generate S (edgeCheapColor B A D) 3).outputs
 have enough:=bothbad_budget_four T S A B C q F proper parents agree ref budget badA badB
 have guard : ¬q<3:=by omega
 change ∃G,(BothBad.execute (GenericForest.solve (PaidInstances.OwnPaid ordinary q)) T S q
  (BothBad.plan S T A B C D q)).answer=some G ∧ agreement T S G=true ∧ G.length≤F.length
 delta BothBad.plan
 by_cases emptyA : a.isEmpty=true
 · by_cases emptyB : b.isEmpty=true
   · obtain ⟨o,member,refF,real⟩:=bothbad_source_cover T S A B C q e F proper parents agree ref budget edge swapped
     have pay : partitionCheck (leaves S) o.partition=true ∧ pairwiseEmbeddings S o.partition=true ∧
       o.partition.length=o.sourceCuts.length+1 ∧ 2≤o.sourceCuts.length := by
      rcases List.mem_append.mp member with left|right
      · exact whole_source_payment T S B A C q (fun _=>0) (sideColor D) (fun _=>0) proper swapped o left real
      · exact whole_source_payment T S A B C q (fun _=>0) (sideColor D) (fun _=>0) proper parents o right real
     have covered:=literal_full_execute_complete ordinary q T S below proper
      ((generate S (edgeCheapColor A B D) q).outputs++(generate S (edgeCheapColor B A D) q).outputs)
      o member pay.1 pay.2.1 pay.2.2.1 (by omega) F agree refF budget
     simpa only [ite_eq_right guard,RankConsumer.fourProbe,←literal_cheapColor A B D,
      ←literal_cheapColor B A D,show (generate S (edgeCheapColor A B D) 3).outputs.isEmpty=true from emptyA,
      show (generate S (edgeCheapColor B A D) 3).outputs.isEmpty=true from emptyB,ite_true] using covered
   · have nonemptyB : b≠[]:=fun h=>emptyB (by rw [h];rfl)
     have refSwap : VertexGeometry.Refines F [B,A,C]:=by
      intro K kF
      obtain ⟨U,uQ,sub⟩:=ref K kF
      exact ⟨U,(List.Perm.swap B A [C]).mem_iff.mp uQ,sub⟩
     have covered:=cheapPlan_coverage ordinary q T S B A C e F below contract proper swapped parents
      (swap_three_embedding S A B C sourceEmb) edge ⟨clearAB.2,clearAB.1⟩ clearBC clearAC
      xb yb xa ya xbB ybB xaA yaA xbD ybN xaD yaN badB goodC agree refSwap budget nonemptyB
     simpa only [ite_eq_right guard,RankConsumer.fourProbe,←literal_cheapColor A B D,
      ←literal_cheapColor B A D,show (generate S (edgeCheapColor A B D) 3).outputs.isEmpty=true from emptyA,
      ite_true,show ¬(generate S (edgeCheapColor B A D) 3).outputs.isEmpty=true from emptyB,Bool.false_eq_true,ite_false] using covered
 · have nonemptyA : a≠[]:=fun h=>emptyA (by rw [h];rfl)
   have covered:=cheapPlan_coverage ordinary q T S A B C e F below contract proper parents swapped sourceEmb edge clearAB
    clearAC clearBC xa ya xb yb xaA yaA xbB ybB xaD yaN xbD ybN badA goodC agree ref budget nonemptyA
   simpa only [ite_eq_right guard,RankConsumer.fourProbe,←literal_cheapColor A B D,
    ←literal_cheapColor B A D,show ¬(generate S (edgeCheapColor A B D) 3).outputs.isEmpty=true from emptyA,Bool.false_eq_true,ite_false] using covered
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.swap_three_embedding
#print axioms ContactedHard2Survival.swap_three_embedding
#check @ContactedHard2Survival.bothbad_budget_four
#print axioms ContactedHard2Survival.bothbad_budget_four
#check @ContactedHard2Survival.cgood_plan_coverage
#print axioms ContactedHard2Survival.cgood_plan_coverage
