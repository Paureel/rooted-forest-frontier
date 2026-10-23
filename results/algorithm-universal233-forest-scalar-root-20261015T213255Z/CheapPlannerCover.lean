import PlannerGeometry
namespace Universal233.BothBad
open RMAF CoreProgram ForestState RestrictionBridge ForestGroups PairAssembly BinaryCheap RankConsumer
open VertexGeometry BinaryExchange

theorem generated_residual_budget (T S : Tree) (color : Nat → Nat) (o : Output) (q0 q : Nat)
    (F : Forest) (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x∈leaves T ↔ x∈leaves S)
    (ho : o∈(generate S color q0).outputs)
    (hF : agreement T S F=true) (href : RestrictionBridge.Refines F o.partition)
    (hq : F.length-1≤q) : o.sourceCuts.length+(F.length-o.partition.length)≤q := by
  obtain ⟨hQ,eQ⟩ := Assembly.generated_source_valid S color q0 o ho
  have fstate := OutputState.original_to_state T S o.partition F ht hs same hQ hF href
  have hmin := ForestGroups.sources_le_blocks _ _ _ fstate
  rw [(OutputState.checked_materialization S o.partition hs hQ).1] at hmin
  have shape := RankDichotomy.generate_partition_cost S color q0 o ho
  omega

theorem cheap_plan_dispatch_cover (solve : ForestSolver) (S T : Tree) (A B C : List Nat)
    (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) (o : Output) (F : Forest)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x∈leaves S ↔ x∈leaves T)
    (hp : partitionCheck (leaves S) [A,B,C]=true)
    (hsource : pairwiseEmbeddings S [A,B,C]=true)
    (hbadA : restrictionAgrees S T A=false) (hbadB : restrictionAgrees S T B=false)
    (hgoodC : restrictionAgrees S T C=true)
    (hchoose : PairGeometry.choose T A B=some (.edge edge))
    (hac : Disj T A C) (hbc : Disj T B C)
    (haccept : fourAccepted S (cheapColor A B (PairGeometry.descendants T edge.2))=true)
    (hq : 3≤q) (hF : agreement T S F=true)
    (ho : o∈outputs S A B (PairGeometry.descendants T edge.2) q)
    (href : RestrictionBridge.Refines F o.partition) (hcost : F.length-1≤q)
    (IH : ExactSolverHyp solve) :
    let D := PairGeometry.descendants T edge.2
    ∃ e H, e∈cheapPlan S T A B C D q (fourProbe S (cheapColor A B D)).outputs
        (reuse S (cheapColor B A D) (fourProbe S (cheapColor B A D)).outputs q) ∧
      (dispatch solve T S e).answer=some H ∧ agreement T S H=true ∧ H.length≤F.length := by
  dsimp only
  let D := PairGeometry.descendants T edge.2
  have same' : ∀ x, x∈leaves T ↔ x∈leaves S := fun x => (same x).symm
  obtain ⟨co,hprobe,hcoCost,hcoLen,hcoPart,hcoSource,hcoTarget,hcoAll,hgood,hbad⟩ :=
    selected_cheap_facts S T A B C edge hs ht same hp hsource hbadA hbadB hgoodC hchoose hac hbc haccept
  change (fourProbe S (cheapColor A B D)).outputs=[co] at hprobe
  have hlist : sideOutputs S B A D q=[co] := hcoAll q hq
  have ranks := selected_ranks S T A B C edge ht (fun x hx => (same x).1 hx) hp hchoose
  have opposite : reuse S (cheapColor B A D) (fourProbe S (cheapColor B A D)).outputs q=
      sideOutputs S A B D q := reuse_exact S _ hs ranks.2 q hq
  change o∈sideOutputs S B A D q ++ sideOutputs S A B D q at ho
  have coGen : co∈(generate S (cheapColor A B D) q).outputs := by
    change co∈sideOutputs S B A D q
    simp [hlist]
  have coCandidate : o=co → ∃ H,
      (dispatch solve T S ⟨co,.ordinary,q-co.sourceCuts.length⟩).answer=some H ∧
      agreement T S H=true ∧ H.length≤F.length := by
    intro he
    subst o
    have budget := generated_residual_budget T S (cheapColor A B D) co q q F hs ht same' coGen hF href hcost
    obtain ⟨H,hH,hAF,hRef,hb,hmin⟩ := global_ordinary_candidate solve T S co.partition
      (q-co.sourceCuts.length) F hs ht hcoPart hcoSource hcoTarget hF href (by omega) IH
    exact ⟨H,hH,hAF,hmin⟩
  cases hg : restrictionAgrees S T (ay A D) && restrictionAgrees S T (an A D) with
  | false =>
    have form : cheapPlan S T A B C D q (fourProbe S (cheapColor A B D)).outputs
        (reuse S (cheapColor B A D) (fourProbe S (cheapColor B A D)).outputs q)=
        entries q .ordinary [co] ++ entries q .full (sideOutputs S A B D q) := by
      simp [cheapPlan,hg,hprobe,opposite]
    rcases List.mem_append.1 ho with ho | ho
    · have he : o=co := by simpa [hlist] using ho
      obtain ⟨H,hH,hAF,hmin⟩ := coCandidate he
      refine ⟨⟨co,.ordinary,q-co.sourceCuts.length⟩,H,?_,hH,hAF,hmin⟩
      rw [form]
      exact List.mem_append.2 (Or.inl (entries_complete q .ordinary [co] co (by simp) (by simp [Mode.extra,hcoCost];omega)))
    · have gen : o∈(generate S (cheapColor B A D) q).outputs := ho
      have hb := generated_residual_budget T S (cheapColor B A D) o q q F hs ht same' gen hF href hcost
      have hQ := (Assembly.generated_source_valid S _ q o gen).1
      obtain ⟨H,hH,hAF,hRef,hB,hmin⟩ := full_candidate solve T S (cheapColor B A D) o q
        (q-o.sourceCuts.length) F hs ht same' gen hF href (by omega)
        (IH _ _ _ (OutputState.sourceForest_proper T S o.partition ht hs same' hQ))
      refine ⟨⟨o,.full,q-o.sourceCuts.length⟩,H,?_,hH,hAF,hmin⟩
      rw [form]
      exact List.mem_append.2 (Or.inr (entries_complete q .full _ o ho (by simpa [Mode.extra] using Nat.le_trans (Nat.le_add_right _ _) hb)))
  | true =>
    obtain ⟨aout,hknown,hsafe⟩ := hgood hg
    have form : cheapPlan S T A B C D q (fourProbe S (cheapColor A B D)).outputs
        (reuse S (cheapColor B A D) (fourProbe S (cheapColor B A D)).outputs q)=
        entries q .ordinary [co] ++ entries q (.retained A B C aout.partition) (sideOutputs S A B D q) := by
      simp [cheapPlan,hg,hknown,hprobe,opposite]
    rcases List.mem_append.1 ho with ho | ho
    · have he : o=co := by simpa [hlist] using ho
      obtain ⟨H,hH,hAF,hmin⟩ := coCandidate he
      refine ⟨⟨co,.ordinary,q-co.sourceCuts.length⟩,H,?_,hH,hAF,hmin⟩
      rw [form]
      exact List.mem_append.2 (Or.inl (entries_complete q .ordinary [co] co (by simp) (by simp [Mode.extra,hcoCost];omega)))
    · have gen : o∈(generate S (cheapColor B A D) q).outputs := ho
      have safe := hsafe q o ho
      have hb := generated_residual_budget T S (cheapColor B A D) o q q F hs ht same' gen hF href hcost
      have lower := retained_paid_lower T S A B C D aout o q F hs ht same' hp ho safe hknown hF href
      have hQ := (Assembly.generated_source_valid S _ q o gen).1
      have own := OutputState.original_source_ownership S o.partition [A,B,C] hs hQ safe.1
      have pB := local_proper (some T) (OutputState.sourceForest S o.partition) [A,B,C]
        (OutputState.sourceForest_proper T S o.partition ht hs same' hQ)
        ((partition_labels_congr _ _ [A,B,C] same').2 hp) own B (by simp)
      obtain ⟨H,hH,hAF,hRef,hB,hmin⟩ := retained_candidate solve T S A B C D aout o q
        (q-o.sourceCuts.length-1) F hs ht same' hp ho safe hknown hgoodC hF href (by omega)
        (IH _ _ _ pB)
      refine ⟨⟨o,.retained A B C aout.partition,q-o.sourceCuts.length-1⟩,H,?_,hH,hAF,hmin⟩
      rw [form]
      exact List.mem_append.2 (Or.inr (entries_complete q (.retained A B C aout.partition) _ o ho (by simp only [Mode.extra];omega)))
end Universal233.BothBad
