import OppositeGroups
namespace OutputState
open RMAF RestrictionBridge ForestState ForestGroups VertexGeometry BinaryExchange
open Universal233 Universal233.CoreProgram Universal233.PairAssembly

theorem full_partition (L : List Nat) (nd : L.Nodup) (ne : L ≠ []) :
    partitionCheck L [L] = true := by
  simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro B hB
    have he : B = L := by simpa using hB
    subst B
    simpa using ne
  · intro x hx
    simp [nd.count,hx]
  · intro x hx
    simpa using hx

theorem retained_C_agreement (T S c : Tree) (A B C : List Nat)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (hrc : restrict C S = some c) (goodC : restrictionAgrees S T C = true) :
    agrees (localTarget (some T) C) [c] [C] = true ∧ additionalCost [c] [C] = 0 := by
  have hqt := (partition_labels_congr _ _ [A,B,C] same).2 hp
  obtain ⟨t,hrt,hlt⟩ := checked_restrictions T [A,B,C] ht hqt C (by simp)
  have hlc := component_labels S c C [A,B,C] hrc hs hp (by simp)
  have partC := full_partition C (RestrictionBridge.checked_block_nodup _ _ hp C (by simp))
    (checked_nonempty _ _ hp C (by simp))
  have pt : partitionCheck (leaves t) [C] = true := (partition_labels_congr _ _ _ (fun x => hlt.mem_iff)).2 partC
  have pc : partitionCheck (leaves c) [C] = true := (partition_labels_congr _ _ _ (fun x => hlc.mem_iff)).2 partC
  have hag : agreement t c [C] = true := by
    have topo := (sameShape_restrict_inside T S t c C C hrt hrc (fun _ hx => hx)).trans
      (restriction_agrees_swap S T C goodC)
    simp [agreement,pt,pc,pairwiseEmbeddings,topo]
  have pstate : proper (some t) [c] = true := by
    simp only [proper,labels,List.map_cons,List.map_nil,Bool.and_eq_true]
    exact ⟨decide_eq_true (restricted_nodup T t C hrt ht),
      (partition_labels_congr (leaves t) (leaves c) [leaves c]
        (fun x => hlt.mem_iff.trans hlc.mem_iff.symm)).2
        (full_partition (leaves c) (restricted_nodup S c C hrc hs) (leaves_nonempty c))⟩
  refine ⟨?_,by rfl⟩
  simpa only [localTarget,Option.bind_some,hrt] using (initial_state_agreement_iff t c [C] pstate).2 hag

/-- The retained local original source-cut certificate supplies the actual
cost-one A ForestState agreement. The original full C agreement supplies cost0.
No mapping or union of original-source cut addresses is asserted. -/
theorem opposite_local_certificates (T S : Tree) (A B C : List Nat) (aout o : Output)
    (a c : Tree) (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (safe : BinaryCheap.OppositeSafe S T A B C aout o)
    (hra : restrict A S = some a) (hrc : restrict C S = some c)
    (goodC : restrictionAgrees S T C = true) :
    agrees (localTarget (some T) A) [a] aout.partition = true ∧
    additionalCost [a] aout.partition = 1 ∧
    agrees (localTarget (some T) C) [c] [C] = true ∧ additionalCost [c] [C] = 0 := by
  obtain ⟨K,hK,hKA,hKS,hKT,hcert⟩ := safe.2.2.2.1
  obtain ⟨s,t,hrs,hrt,hreal,hag,hcost⟩ := hcert
  have hrsA : restrict A S = some s := hKS.symm.trans hrs
  have hrtA : restrict A T = some t := hKT.symm.trans hrt
  have he : s = a := Option.some.inj (hrsA.symm.trans hra)
  subst s
  have hqt := (partition_labels_congr _ _ [A,B,C] same).2 hp
  have hla := component_labels S a A [A,B,C] hra hs hp (by simp)
  have hlt := component_labels T t A [A,B,C] hrtA ht hqt (by simp)
  have pstate : proper (some t) [a] = true := by
    simp only [proper,labels,List.map_cons,List.map_nil,Bool.and_eq_true]
    exact ⟨decide_eq_true (restricted_nodup T t A hrtA ht),
      (partition_labels_congr (leaves t) (leaves a) [leaves a]
        (fun x => hlt.mem_iff.trans hla.mem_iff.symm)).2
        (full_partition (leaves a) (restricted_nodup S a A hra hs) (leaves_nonempty a))⟩
  have ha : agrees (localTarget (some T) A) [a] aout.partition = true := by
    simpa only [localTarget,Option.bind_some,hrtA] using
      (initial_state_agreement_iff t a aout.partition pstate).2 (agreement_swap a t aout.partition hag)
  obtain ⟨hg,hact,components,hroots,hblocks,hprops,hnd,hcov,hsep,hno,hlen⟩ := hreal
  have ca : additionalCost [a] aout.partition = 1 := by
    simp only [additionalCost,List.length_singleton]
    omega
  exact ⟨ha,ca,retained_C_agreement T S c A B C hs ht same hp hrc goodC⟩
end OutputState
