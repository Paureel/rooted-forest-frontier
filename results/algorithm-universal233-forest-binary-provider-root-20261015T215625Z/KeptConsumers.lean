import KeptParent

namespace Universal233.KeptParent
open RMAF CoreProgram Integration CutRealization

theorem shared_block_eq (bs : List (List Nat)) (hn : bs.flatten.Nodup)
    (K L : List Nat) (hK : K ∈ bs) (hL : L ∈ bs)
    (x : Nat) (hxK : x ∈ K) (hxL : x ∈ L) : K = L := by
  induction bs with
  | nil => simp at hK
  | cons b rest ih =>
    have hh := List.nodup_append.1 hn
    simp only [List.mem_cons] at hK hL
    rcases hK with rfl | hK
    · rcases hL with rfl | hL
      · rfl
      · exact False.elim (hh.2.2 x hxK x (List.mem_flatten.2 ⟨L,hL,hxL⟩) rfl)
    · rcases hL with rfl | hL
      · exact False.elim (hh.2.2 x hxL x (List.mem_flatten.2 ⟨K,hK,hxK⟩) rfl)
      · exact ih hh.2.1 hK hL

theorem blocks_nodup (bs : List (List Nat)) (hn : bs.flatten.Nodup)
    (he : ∀ b, b ∈ bs → b ≠ []) : bs.Nodup := by
  induction bs with
  | nil => simp
  | cons b rest ih =>
    have hh := List.nodup_append.1 hn
    apply List.nodup_cons.2
    constructor
    · intro hb
      cases b with
      | nil => exact he [] (by simp) rfl
      | cons x xs =>
        exact hh.2.2 x (by simp) x (List.mem_flatten.2 ⟨x :: xs,hb,by simp⟩) rfl
    · exact ih hh.2.1 (by intro b hb; exact he b (by simp [hb]))

/-- Literal source partition checking rules out two copies of an A block,
including two differently ordered lists with the same nonempty membership. -/
theorem generated_unique_kept (S : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate S color q).outputs) (A : List Nat) (ha : A ≠ []) (hk : Keeps A o) :
    ∃ K, K ∈ o.partition ∧ SameMembers K A ∧ o.partition.count K = 1 ∧
      ∀ L, L ∈ o.partition → SameMembers L A → L = K := by
  obtain ⟨K,hK,hKA⟩ := hk
  have hpart := generate_partition_check S color q o ho
  have hflat : o.partition.flatten.Nodup :=
    (generate_payload_perm S color q o ho).symm.nodup (generate_finish_trace S color q o ho).1
  have hblocks := blocks_nodup o.partition hflat (SourceCoverage.partitionCheck_nonempty _ _ hpart)
  refine ⟨K,hK,hKA,(List.nodup_iff_count_of_mem.1 hblocks) K hK,?_⟩
  intro L hL hLA
  cases A with
  | nil => exact False.elim (ha rfl)
  | cons x xs =>
    exact shared_block_eq o.partition hflat L K hL hK x ((hLA x).2 (by simp)) ((hKA x).2 (by simp))

theorem restrict_same_members (K A : List Nat) (hm : SameMembers K A) (T : Tree) :
    restrict K T = restrict A T := by
  induction T with
  | leaf x => simp only [restrict,List.contains_iff_mem,hm x]
  | node l r ihl ihr => simp only [restrict,ihl,ihr]

theorem restriction_agrees_same_members (S T : Tree) (K A : List Nat)
    (hm : SameMembers K A) : restrictionAgrees S T K = restrictionAgrees S T A := by
  simp only [restrictionAgrees,restrict_same_members K A hm]

/-- The same ORIGINAL restricted trees and the same labelled local forest.
No new local namespace or suppression display is substituted. -/
def LocalCompletion (S T : Tree) (A : List Nat) (F : List (List Nat)) : Prop :=
  ∃ s t, restrict A S = some s ∧ restrict A T = some t ∧ agreement s t F = true

theorem local_completion_same_members (S T : Tree) (K A : List Nat) (F : List (List Nat))
    (hm : SameMembers K A) (hf : LocalCompletion S T A F) : LocalCompletion S T K F := by
  obtain ⟨s,t,hs,ht,hf⟩ := hf
  exact ⟨s,t,(restrict_same_members K A hm S).trans hs,
    (restrict_same_members K A hm T).trans ht,hf⟩

/-- Each actual output retains the original nonhomeomorphic A problem and a
supplied two-piece local agreement at the paid one-cut local charge. This holds
for every output, hence for every B-clear output as well. It does not lift a
local restricted-tree source edge to an original S address or discount q. -/
theorem every_output_retains_paid_A (S T : Tree) (A B C : List Nat) (cb : Nat → Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (he : pairwiseEmbeddings S [A,B,C] = true)
    (hbad : restrictionAgrees S T A = false)
    (F : List (List Nat)) (hf : LocalCompletion S T A F) (hcost : F.length = 2)
    (q : Nat) (o : Output) (ho : o ∈ (generate S (keepColor A B cb) q).outputs) :
    ∃ K, K ∈ o.partition ∧ SameMembers K A ∧
      restrict K S = restrict A S ∧ restrict K T = restrict A T ∧
      restrictionAgrees S T K = false ∧ LocalCompletion S T K F ∧ F.length - 1 = 1 := by
  obtain ⟨K,hK,hKA⟩ := (generated_keeps_A_C S A B C cb hp he q o ho).1
  exact ⟨K,hK,hKA,restrict_same_members K A hKA S,restrict_same_members K A hKA T,
    (restriction_agrees_same_members S T K A hKA).trans hbad,
    local_completion_same_members S T K A F hKA hf,by omega⟩


/-- A supplied local source-cut certificate is measured on the original
restricted A tree, with actual original local addresses and local charge one. -/
def OriginalLocalOneCut (S T : Tree) (A : List Nat) (a : Output) : Prop :=
  ∃ s t, restrict A S = some s ∧ restrict A T = some t ∧
    RealizedOutput s a ∧ agreement s t a.partition = true ∧ a.sourceCuts.length = 1

theorem original_local_one_cut_same_members (S T : Tree) (K A : List Nat) (a : Output)
    (hm : SameMembers K A) (hf : OriginalLocalOneCut S T A a) : OriginalLocalOneCut S T K a := by
  obtain ⟨s,t,hs,ht,hreal,hagree,hcost⟩ := hf
  exact ⟨s,t,(restrict_same_members K A hm S).trans hs,
    (restrict_same_members K A hm T).trans ht,hreal,hagree,hcost⟩

theorem every_output_retains_original_local_cut (S T : Tree) (A B C : List Nat) (cb : Nat → Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (he : pairwiseEmbeddings S [A,B,C] = true)
    (a : Output) (ha : OriginalLocalOneCut S T A a)
    (q : Nat) (o : Output) (ho : o ∈ (generate S (keepColor A B cb) q).outputs) :
    ∃ K, K ∈ o.partition ∧ SameMembers K A ∧ OriginalLocalOneCut S T K a := by
  obtain ⟨K,hK,hKA⟩ := (generated_keeps_A_C S A B C cb hp he q o ho).1
  exact ⟨K,hK,hKA,original_local_one_cut_same_members S T K A a hKA ha⟩

end Universal233.KeptParent
