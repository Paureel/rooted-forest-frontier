import SelectedContinuation
import Permutation
namespace OutputState
open RMAF RestrictionBridge ForestState ForestGroups VertexGeometry BinaryExchange
open Universal233 Universal233.CoreProgram Universal233.PairAssembly

theorem generated_source_bridge (T S : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate S color q).outputs)
    (properT : (leaves T).Nodup) (properS : (leaves S).Nodup)
    (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S) :
    proper (some T) (sourceForest S o.partition) = true ∧
    (sourceForest S o.partition).length = o.partition.length ∧
    (∀ F, agrees (some T) (sourceForest S o.partition) F = true ↔
      agreement T S F = true ∧ RestrictionBridge.Refines F o.partition) ∧
    (∀ F, additionalCost (sourceForest S o.partition) F = F.length - o.partition.length) := by
  obtain ⟨hp,he⟩ := Assembly.generated_source_valid S color q o ho
  exact ⟨sourceForest_proper T S o.partition properT properS same hp,
    (checked_materialization S o.partition properS hp).1,
    fun F => agrees_iff_original T S o.partition F properT properS same hp he,
    fun F => exact_additional_cost S o.partition F properS hp⟩

theorem sourceForest_nodup (S : Tree) (Q : List (List Nat))
    (hs : (leaves S).Nodup) (hQ : partitionCheck (leaves S) Q = true) :
    (sourceForest S Q).Nodup := by
  exact List.Pairwise.of_map leaves (fun a b h he => h (congrArg leaves he))
    (checked_family_nodup _ _ (materialized_partition S Q hs hQ))

theorem singleton_of_unique (ss : List Tree) (a : Tree) (ha : a ∈ ss)
    (nd : ss.Nodup) (one : ∀ s ∈ ss, s = a) : ss = [a] := by
  cases ss with
  | nil => simp at ha
  | cons r rs =>
    have hr := one r (by simp)
    subst r
    have hz : rs = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro s hs
      have he := one s (by simp [hs])
      subst s
      exact (List.nodup_cons.1 nd).1 hs
    simp [hz]

/-- A retained full label class determines one unique literal current source
component even when its output label order differs from the parent order. -/
theorem retained_owned (S : Tree) (Q : List (List Nat)) (A : List Nat)
    (hs : (leaves S).Nodup) (hQ : partitionCheck (leaves S) Q = true)
    (hA : A.Nodup) (keep : ∃ K ∈ Q, KeptParent.SameMembers K A) :
    ∃ a, restrict A S = some a ∧ (leaves a).Perm A ∧
      owned (sourceForest S Q) A = [a] := by
  obtain ⟨K,hK,hKA⟩ := keep
  obtain ⟨a,hra,hla⟩ := checked_restrictions S Q hs hQ K hK
  have hrA : restrict A S = some a := (KeptParent.restrict_same_members K A hKA S).symm.trans hra
  have hAK : A.Perm K := (List.perm_ext_iff_of_nodup hA
    (RestrictionBridge.checked_block_nodup (leaves S) Q hQ K hK)).2 (fun x => (hKA x).symm)
  have hlaA : (leaves a).Perm A := hla.trans hAK.symm
  have hm : a ∈ owned (sourceForest S Q) A := (mem_owned _ _ _).2
    ⟨(source_component S Q a).2 ⟨K,hK,hra⟩,fun x hx => hlaA.mem_iff.1 hx⟩
  refine ⟨a,hrA,hlaA,singleton_of_unique _ a hm ?_ ?_⟩
  · exact (sourceForest_nodup S Q hs hQ).filter _
  · intro s hsm
    obtain ⟨hss,hsA⟩ := (mem_owned s (sourceForest S Q) A).1 hsm
    obtain ⟨U,hU,hru⟩ := (source_component S Q s).1 hss
    have hlu := component_labels S s U Q hru hs hQ hU
    obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil (leaves s) (leaves_nonempty s)
    have hxU := hlu.mem_iff.1 hx
    have hxK := (hKA x).2 (hsA hx)
    have eq := group_unique (leaves S) Q hQ U K hU hK x hxU hxK
    subst U
    exact Option.some.inj (hru.symm.trans hra)

theorem original_source_ownership (S : Tree) (Q : List (List Nat)) (P : List (List Nat))
    (hs : (leaves S).Nodup) (hQ : partitionCheck (leaves S) Q = true)
    (refines : SourceCoverage.RefinesBlocks Q P) : Owns (sourceForest S Q) P := by
  intro s hsm
  obtain ⟨U,hU,hru⟩ := (source_component S Q s).1 hsm
  obtain ⟨V,hV,hUV⟩ := refines U hU
  have hlu := component_labels S s U Q hru hs hQ hU
  exact ⟨V,hV,fun x hx => hUV x (hlu.mem_iff.1 hx)⟩

/-- Every actual opposite B-clear output gives a literal A / whole B-forest / C
reordering, proved to preserve the checker and cost. No clearance is required
between distinct B pieces. -/
theorem opposite_grouping (T S : Tree) (A B C D : List Nat) (aout o : Output) (q : Nat)
    (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
    (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (ho : o ∈ sideOutputs S A B D q)
    (safe : BinaryCheap.OppositeSafe S T A B C aout o) :
    ∃ a c, restrict A S = some a ∧ restrict C S = some c ∧
      (leaves a).Perm A ∧ (leaves c).Perm C ∧
      owned (sourceForest S o.partition) A = [a] ∧
      owned (sourceForest S o.partition) C = [c] ∧
      (sourceForest S o.partition).Perm ([a] ++ owned (sourceForest S o.partition) B ++ [c]) ∧
      proper (some T) ([a] ++ owned (sourceForest S o.partition) B ++ [c]) = true ∧
      PriorityClear (some T) a (owned (sourceForest S o.partition) B) [c] := by
  have hgen : o ∈ (generate S (Assembly.taggedColor A B (fun _ => 0) (sideColor D) (fun _ => 0)) q).outputs := ho
  obtain ⟨hQ,eQ⟩ := Assembly.generated_source_valid S _ q o hgen
  obtain ⟨a,hra,hla,ownA⟩ := retained_owned S o.partition A hs hQ (RestrictionBridge.checked_block_nodup _ _ hp A (by simp)) safe.2.1
  obtain ⟨c,hrc,hlc,ownC⟩ := retained_owned S o.partition C hs hQ (RestrictionBridge.checked_block_nodup _ _ hp C (by simp)) safe.2.2.1
  have hqt := (partition_labels_congr _ _ [A,B,C] same).2 hp
  have own := original_source_ownership S o.partition [A,B,C] hs hQ safe.1
  have perm : (sourceForest S o.partition).Perm ([a] ++ owned (sourceForest S o.partition) B ++ [c]) := by
    simpa only [ownA,ownC] using owned_three_permutation (some T) (sourceForest S o.partition) A B C hqt own
  have hproper := sourceForest_proper T S o.partition ht hs same hQ
  have proper' : proper (some T) ([a] ++ owned (sourceForest S o.partition) B ++ [c]) = true := by
    simp only [proper,Bool.and_eq_true] at hproper ⊢
    exact ⟨hproper.1,(partition_permutation _ _ _ (perm.map leaves)).symm.trans hproper.2⟩
  refine ⟨a,c,hra,hrc,hla,hlc,ownA,ownC,perm,proper',?_⟩
  intro t heq
  have he : t = T := Option.some.inj heq.symm
  subst t
  have clearB : ∀ b ∈ owned (sourceForest S o.partition) B,
      Clear (minimalVertices (leaves b) T) (minimalVertices A T) ∧
      Clear (minimalVertices (leaves b) T) (minimalVertices C T) := by
    intro b hb
    obtain ⟨hbs,hbB⟩ := (mem_owned _ _ _).1 hb
    obtain ⟨L,hL,hrL⟩ := (source_component S o.partition b).1 hbs
    have hl := component_labels S b L o.partition hrL hs hQ hL
    have sub : Sub L B := fun x hx => hbB (hl.mem_iff.2 hx)
    obtain ⟨hLA,hLC⟩ := safe.2.2.2.2.1 L hL sub
    have cLA := (clear_iff _ _).1 ((executable_disjointVertices T L A).2 hLA)
    have cLC := (clear_iff _ _).1 ((executable_disjointVertices T L C).2 hLC)
    exact ⟨fun v hv ha => cLA v (executable_span_monotone T (leaves b) L (fun x hx => hl.mem_iff.1 hx) v hv) ha,
      fun v hv hc => cLC v (executable_span_monotone T (leaves b) L (fun x hx => hl.mem_iff.1 hx) v hv) hc⟩
  have ac := (clear_iff _ _).1 ((executable_disjointVertices T A C).2 safe.2.2.2.2.2)
  refine ⟨?_,?_,?_⟩
  · intro b hb v ha hbv
    exact (clearB b hb).1 v hbv (executable_span_monotone T (leaves a) A (fun x hx => hla.mem_iff.1 hx) v ha)
  · intro c' hc'
    have he : c' = c := by simpa using hc'
    subst c'
    intro v ha hc
    exact ac v (executable_span_monotone T (leaves a) A (fun x hx => hla.mem_iff.1 hx) v ha)
      (executable_span_monotone T (leaves c) C (fun x hx => hlc.mem_iff.1 hx) v hc)
  · intro b hb c' hc'
    have he : c' = c := by simpa using hc'
    subst c'
    intro v hbv hc
    exact (clearB b hb).2 v hbv
      (executable_span_monotone T (leaves c) C (fun x hx => hlc.mem_iff.1 hx) v hc)
end OutputState
