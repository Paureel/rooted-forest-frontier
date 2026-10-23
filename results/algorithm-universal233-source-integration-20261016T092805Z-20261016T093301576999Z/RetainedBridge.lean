import OrdinaryBridge
namespace Universal233.BothBad
open RMAF CoreProgram ForestState RestrictionBridge ForestGroups PairAssembly

/-- The cost-one subtraction is justified against EVERY feasible original F.
The actual child is the whole current B forest, whose pieces may overlap on T. -/
theorem retained_candidate (solve : ForestSolver) (T S : Tree) (A B C D : List Nat)
    (aout o : Output) (q0 b : Nat) (F : Forest)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x∈leaves T ↔ x∈leaves S)
    (hp : partitionCheck (leaves S) [A,B,C]=true)
    (ho : o∈sideOutputs S A B D q0)
    (safe : BinaryCheap.OppositeSafe S T A B C aout o)
    (hk : knownOne T S A=some aout.partition)
    (goodC : restrictionAgrees S T C=true)
    (hF : agreement T S F=true) (href : Refines F o.partition)
    (hbudget : F.length-o.partition.length≤b+1)
    (IH : ExactAt solve (localTarget (some T) B)
      (owned (OutputState.sourceForest S o.partition) B) b) :
    ∃ H, (dispatch solve T S ⟨o,.retained A B C aout.partition,b⟩).answer=some H ∧
      agreement T S H=true ∧ Refines H o.partition ∧
      H.length-o.partition.length≤b+1 ∧ H.length≤F.length := by
  obtain ⟨hQ,eQ⟩ := Assembly.generated_source_valid S _ q0 o ho
  obtain ⟨a,c,hra,hrc,hla,hlc,ownA,ownC,perm,proper',clear⟩ :=
    OutputState.opposite_grouping T S A B C D aout o q0 hs ht same hp ho safe
  have hqt : partitionCheck (labels (some T)) [A,B,C]=true :=
    (partition_labels_congr _ _ [A,B,C] same).2 hp
  have own := OutputState.original_source_ownership S o.partition [A,B,C] hs hQ safe.1
  have fstate := OutputState.original_to_state T S o.partition F ht hs same hQ hF href
  have fA := ForestGroups.local_forward (some T) (OutputState.sourceForest S o.partition)
    [A,B,C] F fstate hqt own A (by simp)
  have fB := ForestGroups.local_forward (some T) (OutputState.sourceForest S o.partition)
    [A,B,C] F fstate hqt own B (by simp)
  have fc := ForestGroups.forward_exact_cost (some T) (OutputState.sourceForest S o.partition)
    [A,B,C] F fstate hqt own
  obtain ⟨t,s,p,hrt,hrs,hfound,hknown,hlocal,hknownCost,hreal,hminA⟩ := knownOne_sound T S A aout.partition hk
  have he : s=a := Option.some.inj (hrs.symm.trans hra)
  subst s
  rw [ownA] at fA
  have initialProper : proper (some t) [a]=true := by
    have pf := (agrees_parts _ _ _ fA).1
    simpa only [localTarget,Option.bind_some,hrt] using pf
  have originalA : agreement t a (family A F)=true :=
    (initial_state_agreement_iff t a _ initialProper).1
      (by simpa only [localTarget,Option.bind_some,hrt] using fA)
  have lowerA : 1≤additionalCost (owned (OutputState.sourceForest S o.partition) A) (family A F) := by
    rw [ownA]
    exact hminA _ originalA
  have hfc : additionalCost (OutputState.sourceForest S o.partition) F=F.length-o.partition.length :=
    OutputState.exact_additional_cost S o.partition F hs hQ
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at fc
  have bcost : additionalCost (owned (OutputState.sourceForest S o.partition) B) (family B F)≤b := by
    omega
  obtain ⟨FB,hquery⟩ := IH.2 (family B F) fB bcost
  obtain ⟨hFB,hFBbudget,hFBminimal⟩ := IH.1 FB hquery
  have minimalB := hFBminimal (family B F) fB
  have lifted := OutputState.every_opposite_residual_query solve T S A B C D aout o q0 (b+1) FB
    hs ht same hp ho safe goodC (by omega) (by
      simpa only [Nat.add_sub_cancel] using exactAt_residual solve _ _ b IH) (by
      simpa only [Nat.add_sub_cancel] using hquery)
  dsimp only at lifted
  refine ⟨aout.partition++FB++[C],?_,lifted.2.1,lifted.2.2.1,lifted.2.2.2.2.2,?_⟩
  · simp only [dispatch,hquery,Option.map_some]
  · have hcost := lifted.2.2.2.1
    rw [OutputState.exact_additional_cost S o.partition _ hs hQ] at hcost
    have hfLen := ForestGroups.sources_le_blocks _ _ _ fstate
    rw [(OutputState.checked_materialization S o.partition hs hQ).1] at hfLen
    omega
end Universal233.BothBad
