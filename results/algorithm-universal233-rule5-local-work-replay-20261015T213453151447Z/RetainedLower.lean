import RetainedBridge
namespace Universal233.BothBad
open RMAF CoreProgram ForestState RestrictionBridge ForestGroups PairAssembly

theorem retained_paid_lower (T S : Tree) (A B C D : List Nat)
    (aout o : Output) (q0 : Nat) (F : Forest)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x∈leaves T ↔ x∈leaves S)
    (hp : partitionCheck (leaves S) [A,B,C]=true)
    (ho : o∈sideOutputs S A B D q0)
    (safe : BinaryCheap.OppositeSafe S T A B C aout o)
    (hk : knownOne T S A=some aout.partition)
    (hF : agreement T S F=true) (href : Refines F o.partition) :
    1≤F.length-o.partition.length := by
  obtain ⟨hQ,eQ⟩ := Assembly.generated_source_valid S _ q0 o ho
  obtain ⟨a,c,hra,hrc,hla,hlc,ownA,ownC,perm,proper',clear⟩ :=
    OutputState.opposite_grouping T S A B C D aout o q0 hs ht same hp ho safe
  have hqt : partitionCheck (labels (some T)) [A,B,C]=true :=
    (partition_labels_congr _ _ [A,B,C] same).2 hp
  have own := OutputState.original_source_ownership S o.partition [A,B,C] hs hQ safe.1
  have fstate := OutputState.original_to_state T S o.partition F ht hs same hQ hF href
  have fA := ForestGroups.local_forward (some T) (OutputState.sourceForest S o.partition)
    [A,B,C] F fstate hqt own A (by simp)
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
  have hfc := OutputState.exact_additional_cost S o.partition F hs hQ
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at fc
  omega

end Universal233.BothBad
