import RetainedLower
namespace Universal233.BothBad
open RMAF CoreProgram ForestState RestrictionBridge ForestGroups PairAssembly BinaryCheap RankConsumer
open VertexGeometry BinaryExchange

def ExactSolverHyp (solve : ForestSolver) : Prop :=
  ∀ t ss b, proper t ss=true → ExactAt solve t ss b

theorem selected_ranks (S T : Tree) (A B C : List Nat) (edge : RMAF.Vertex × RMAF.Vertex)
    (ht : (leaves T).Nodup) (hl : ∀ x, x∈leaves S → x∈leaves T)
    (hp : partitionCheck (leaves S) [A,B,C]=true)
    (hchoose : PairGeometry.choose T A B=some (.edge edge)) :
    RankDichotomy.inputRank S (cheapColor A B (PairGeometry.descendants T edge.2))=4 ∧
    RankDichotomy.inputRank S (cheapColor B A (PairGeometry.descendants T edge.2))=4 := by
  obtain ⟨u,hu,hyA,hnA,hyB,hnB,_⟩ := edge_facts T A B edge hchoose
  have hd : ∀ U, ay U (PairGeometry.descendants T edge.2)=ay U (leaves u) ∧
      an U (PairGeometry.descendants T edge.2)=an U (leaves u) := by
    intro U
    exact ⟨FreshPairReview.side_yes U T u edge.2 ht hu,FreshPairReview.side_no U T u edge.2 ht hu⟩
  exact ⟨cheap_rank S T A B C _ hp ht hl (by rw [(hd A).1];exact hyA) (by rw [(hd A).2];exact hnA),
    cheap_rank S T B A C _ (partition_swap _ A B C hp) ht hl
      (by rw [(hd B).1];exact hyB) (by rw [(hd B).2];exact hnB)⟩

theorem selected_cheap_facts (S T : Tree) (A B C : List Nat)
    (edge : RMAF.Vertex × RMAF.Vertex)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x∈leaves S ↔ x∈leaves T)
    (hp : partitionCheck (leaves S) [A,B,C]=true)
    (hsource : pairwiseEmbeddings S [A,B,C]=true)
    (hbadA : restrictionAgrees S T A=false) (hbadB : restrictionAgrees S T B=false)
    (hgoodC : restrictionAgrees S T C=true)
    (hchoose : PairGeometry.choose T A B=some (.edge edge))
    (hac : Disj T A C) (hbc : Disj T B C)
    (haccept : fourAccepted S (cheapColor A B (PairGeometry.descendants T edge.2))=true) :
    let D := PairGeometry.descendants T edge.2
    ∃ o, (fourProbe S (cheapColor A B D)).outputs=[o] ∧
      o.sourceCuts.length=3 ∧ o.partition.length=4 ∧
      partitionCheck (leaves S) o.partition=true ∧ pairwiseEmbeddings S o.partition=true ∧
      pairwiseEmbeddings T o.partition=true ∧
      (∀ q, 3≤q → sideOutputs S B A D q=[o]) ∧
      ((restrictionAgrees S T (ay A D) && restrictionAgrees S T (an A D))=true →
        ∃ aout, knownOne T S A=some aout.partition ∧
          ∀ q z, z∈sideOutputs S A B D q → OppositeSafe S T A B C aout z) ∧
      ((restrictionAgrees S T (ay A D) && restrictionAgrees S T (an A D))=false → TwoBad S T o) := by
  dsimp only
  obtain ⟨u,o,hu,hout,hcost,hlen,hpart,hsrc,htgt,hfor,hback,hC,hall,hgood,hbad⟩ :=
    selected_cheap_continuation S T A B C edge hs ht same hp hsource hbadA hbadB hgoodC hchoose hac hbc haccept
  have hd : ay A (PairGeometry.descendants T edge.2)=ay A (leaves u) ∧
      an A (PairGeometry.descendants T edge.2)=an A (leaves u) :=
    ⟨FreshPairReview.side_yes A T u edge.2 ht hu,FreshPairReview.side_no A T u edge.2 ht hu⟩
  refine ⟨o,hout,hcost,hlen,hpart,hsrc,htgt,hall,?_,?_⟩
  · intro hg
    rw [hd.1,hd.2] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨s,t,p,hrs,hrt,hfound,hcert,hmin,hsafe⟩ := hgood hg.1 hg.2
    exact ⟨⟨DepthOne.forest s (some p),[p]⟩,by simp [knownOne,hrt,hrs,hfound],hsafe⟩
  · intro hg
    apply hbad
    intro hboth
    rw [hd.1,hd.2] at hg
    simp [hboth.1,hboth.2] at hg

theorem global_ordinary_candidate (solve : ForestSolver) (T S : Tree) (Q : Forest) (b : Nat) (F : Forest)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (hQ : partitionCheck (leaves S) Q=true) (eS : pairwiseEmbeddings S Q=true)
    (eT : pairwiseEmbeddings T Q=true)
    (hF : agreement T S F=true) (href : RestrictionBridge.Refines F Q) (hbudget : F.length-Q.length≤b)
    (IH : ExactSolverHyp solve) :
    ∃ H, (ordinaryExecution solve T S Q b).answer=some H ∧
      agreement T S H=true ∧ RestrictionBridge.Refines H Q ∧ H.length-Q.length≤b ∧ H.length≤F.length := by
  apply ordinary_candidate solve T S Q b F hs ht hQ eS eT hF href hbudget
  intro U hU t s hrt hrs k
  have hh:=hF
  simp only [agreement,Bool.and_eq_true] at hh
  have hQT : partitionCheck (leaves T) Q=true :=
    (partition_labels_congr _ _ Q (checked_labels_iff _ _ F hh.1.1.1.1 hh.1.1.1.2)).2 hQ
  have lt := component_labels T t U Q hrt ht hQT hU
  have ls := component_labels S s U Q hrs hs hQ hU
  have localProper : DepthOne.proper t s=true := (DepthOne.proper_iff _ _).2
    ⟨restricted_nodup T t U hrt ht,restricted_nodup S s U hrs hs,lt.trans ls.symm⟩
  exact IH (some t) [s] k (single_state_proper t s localProper)

end Universal233.BothBad
