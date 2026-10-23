import KeptConsumers

namespace NonauthorKeptConsumer
open RMAF Universal233 CoreProgram KeptParent CutRealization Integration

/-- The complete root-pin interface: unique untouched parents, every other
literal block in B, and unchanged original restrictions for arbitrary targets. -/
theorem original_interface (S : Tree) (A B C : List Nat) (beta : Nat → Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (he : pairwiseEmbeddings S [A,B,C] = true)
    (q : Nat) (o : Output) (ho : o ∈ (generate S (keepColor A B beta) q).outputs) :
    ∃ KA KC, KA ∈ o.partition ∧ KC ∈ o.partition ∧
      SameMembers KA A ∧ SameMembers KC C ∧
      o.partition.count KA = 1 ∧ o.partition.count KC = 1 ∧ KA ≠ KC ∧
      (∀ L, L ∈ o.partition → SameMembers L A → L = KA) ∧
      (∀ L, L ∈ o.partition → SameMembers L C → L = KC) ∧
      (∀ L, L ∈ o.partition → L ≠ KA → L ≠ KC → ∀ x, x ∈ L → x ∈ B) ∧
      (∀ T, restrict KA T = restrict A T ∧ restrict KC T = restrict C T) := by
  have hane := SourceCoverage.partitionCheck_nonempty (leaves S) [A,B,C] hp A (by simp)
  have hcne := SourceCoverage.partitionCheck_nonempty (leaves S) [A,B,C] hp C (by simp)
  have hkept := generated_keeps_A_C S A B C beta hp he q o ho
  obtain ⟨KA,hKA,hA,hcountA,huniqA⟩ := generated_unique_kept S (keepColor A B beta) q o ho A hane hkept.1
  obtain ⟨KC,hKC,hC,hcountC,huniqC⟩ := generated_unique_kept S (keepColor A B beta) q o ho C hcne hkept.2
  have hflat : o.partition.flatten.Nodup :=
    (generate_payload_perm S (keepColor A B beta) q o ho).symm.nodup
      (generate_finish_trace S (keepColor A B beta) q o ho).1
  refine ⟨KA,KC,hKA,hKC,hA,hC,hcountA,hcountC,?_,huniqA,huniqC,?_,?_⟩
  · intro hsame
    cases A with
    | nil => exact hane rfl
    | cons x xs =>
      have hxA : x ∈ KA := (hA x).2 (by simp)
      have hxC : x ∈ C := (hC x).1 (hsame ▸ hxA)
      exact (checked_parent_disjoint S (x :: xs) B C hp).2.1 x (by simp) hxC
  · intro L hL hnA hnC x hx
    have hsource : x ∈ leaves S :=
      (generate_payload_perm S (keepColor A B beta) q o ho).mem_iff.1
        (List.mem_flatten.2 ⟨L,hL,hx⟩)
    obtain ⟨p,hp',hxp⟩ := partitionCheck_covers (leaves S) [A,B,C] hp x hsource
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    · exact False.elim (hnA (shared_block_eq o.partition hflat L KA hL hKA x hx ((hA x).2 hxp)))
    · exact hxp
    · exact False.elim (hnC (shared_block_eq o.partition hflat L KC hL hKC x hx ((hC x).2 hxp)))
  · intro T
    exact ⟨restrict_same_members KA A hA T,restrict_same_members KC C hC T⟩

/-- Caller-supplied original LOCAL cut survives with identical certificate;
this statement creates no whole-source cut and changes no query budget. -/
theorem retained_original_local (S T : Tree) (A B C : List Nat) (beta : Nat → Nat)
    (hp : partitionCheck (leaves S) [A,B,C] = true)
    (he : pairwiseEmbeddings S [A,B,C] = true)
    (a : Output) (ha : OriginalLocalOneCut S T A a)
    (q : Nat) (o : Output) (ho : o ∈ (generate S (keepColor A B beta) q).outputs) :
    ∃ K, K ∈ o.partition ∧ SameMembers K A ∧
      restrict K S = restrict A S ∧ restrict K T = restrict A T ∧
      OriginalLocalOneCut S T K a ∧ a.sourceCuts.length = 1 := by
  obtain ⟨K,hK,hm,hlocal⟩ := every_output_retains_original_local_cut S T A B C beta hp he a ha q o ho
  obtain ⟨s,t,hs,ht,hr,hag,hcost⟩ := ha
  exact ⟨K,hK,hm,restrict_same_members K A hm S,restrict_same_members K A hm T,hlocal,hcost⟩

def S : Tree := .node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
    (.node (.leaf 3) (.leaf 4))) (.leaf 5)
def T : Tree := .node (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))
    (.node (.leaf 3) (.leaf 4))) (.leaf 5)
def A : List Nat := [0,1,2]
def B : List Nat := [3,4]
def C : List Nat := [5]
def beta (_ : Nat) : Nat := 0

theorem source_partition : partitionCheck (leaves S) [A,B,C] = true := by decide
theorem source_embeddings : pairwiseEmbeddings S [A,B,C] = true := by decide
theorem original_bad : restrictionAgrees S T A = false := by decide

def localS : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def localT : Tree := .node (.leaf 0) (.node (.leaf 1) (.leaf 2))
def localColor (x : Nat) : Nat := if x = 0 then 0 else 1
def localOne : Output := ⟨[[0],[1,2]],[[false,false]]⟩
theorem local_emitted : localOne ∈ (generate localS localColor 1).outputs := by decide
theorem local_actual : OriginalLocalOneCut S T A localOne := by
  refine ⟨localS,localT,by decide,by decide,?_,by decide,by decide⟩
  exact generate_original_realization localS localColor 1 localOne local_emitted

theorem every_fixture_output (q : Nat) (o : Output)
    (ho : o ∈ (generate S (keepColor A B beta) q).outputs) :
    ∃ K, K ∈ o.partition ∧ SameMembers K A ∧
      restrict K S = restrict A S ∧ restrict K T = restrict A T ∧
      OriginalLocalOneCut S T K localOne ∧ localOne.sourceCuts.length = 1 :=
  retained_original_local S T A B C beta source_partition source_embeddings localOne local_actual q o ho

def localF : List (List Nat) := [[0],[1,2]]
theorem local_completion : LocalCompletion S T A localF := by
  exact ⟨localS,localT,by decide,by decide,by decide⟩
theorem every_fixture_paid (q : Nat) (o : Output)
    (ho : o ∈ (generate S (keepColor A B beta) q).outputs) :
    ∃ K, K ∈ o.partition ∧ SameMembers K A ∧
      restrict K S = restrict A S ∧ restrict K T = restrict A T ∧
      restrictionAgrees S T K = false ∧ LocalCompletion S T K localF ∧ localF.length - 1 = 1 :=
  every_output_retains_paid_A S T A B C beta source_partition source_embeddings original_bad
    localF local_completion (by decide) q o ho

end NonauthorKeptConsumer
