import Permutations

namespace Universal233.FinalCutRecovery
open RMAF CoreProgram SourceCoverage VertexGeometry RankDichotomy

theorem inputCheck_iff (S : Tree) (P : List (List Nat)) : inputCheck S P = true ↔
    (leaves S).Nodup ∧ partitionCheck (leaves S) P = true ∧ pairwiseEmbeddings S P = true := by
  simp only [inputCheck,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hn,hp⟩,he⟩; exact ⟨hn,hp,he⟩
  · rintro ⟨hn,hp,he⟩; exact ⟨⟨hn,hp⟩,he⟩

theorem rejected_input (S : Tree) (P : List (List Nat)) (h : inputCheck S P = false) :
    recover S P = none := by simp [recover,h]

theorem recover_some_guards (S : Tree) (P : List (List Nat)) (o : Output)
    (h : recover S P = some o) :
    (leaves S).Nodup ∧ partitionCheck (leaves S) P = true ∧ pairwiseEmbeddings S P = true := by
  unfold recover at h
  split at h
  · exact (inputCheck_iff S P).1 (by assumption)
  · contradiction

/-- Executable final-output recovery at the literal |P|-1 budget. Every theorem
input is an ordinary input check; rank equality, output existence, original
realization, nonredundancy, and exact partition semantics are conclusions. -/
theorem recover_checked (S : Tree) (P : List (List Nat))
    (hn : (leaves S).Nodup) (hp : partitionCheck (leaves S) P = true)
    (he : pairwiseEmbeddings S P = true) :
    ∃ o, recover S P = some o ∧
      (generate S (blockColor P) (P.length - 1)).outputs = [o] ∧
      o.sourceCuts.length = P.length - 1 ∧ o.partition.length = P.length ∧
      CutRealization.RealizedOutput S o ∧ BlockPermutation P o.partition ∧
      partitionCheck (leaves S) o.partition = true := by
  have hr := checked_rank S P hp
  have hf : RankFeasible S (blockColor P) :=
    ⟨P,hp,he,checked_monochromatic S P hp,hr.symm⟩
  obtain ⟨o,ho,hcost⟩ := feasible_unique S (blockColor P) hn hf (P.length - 1) (by omega)
  have hmem : o ∈ (generate S (blockColor P) (P.length - 1)).outputs := by rw [ho]; simp
  have hcheck := CutRealization.generate_partition_check S (blockColor P) _ o hmem
  have hmono := CutRealization.generate_monochromatic S (blockColor P) _ o hmem
  have hpcount := generate_partition_cost S (blockColor P) _ o hmem
  have hpos := inputRank_pos S (blockColor P)
  have hc : o.sourceCuts.length = P.length - 1 := by omega
  have hlen : o.partition.length = P.length := by omega
  refine ⟨o,?_,ho,hc,hlen,CutRealization.generate_original_realization S (blockColor P) _ o hmem,
    checked_block_permutation S P o.partition hp hcheck hmono hlen,hcheck⟩
  have hguard := (inputCheck_iff S P).2 ⟨hn,hp,he⟩
  simp only [recover,hguard,ite_true,ho,List.head?_cons]

/-- Soundness for the literal returned certificate, including exact original
component reconstruction and exact nonredundant cost. -/
theorem recover_sound (S : Tree) (P : List (List Nat)) (o : Output)
    (ho : recover S P = some o) :
    CutRealization.RealizedOutput S o ∧ o.sourceCuts.length = P.length - 1 ∧
      o.partition.length = P.length ∧ BlockPermutation P o.partition ∧
      partitionCheck (leaves S) o.partition = true := by
  obtain ⟨hn,hp,he⟩ := recover_some_guards S P o ho
  obtain ⟨o',ho',_,hc,hl,hr,hperm,hcheck⟩ := recover_checked S P hn hp he
  have heq : o' = o := Option.some.inj (ho'.symm.trans ho)
  subst o'
  exact ⟨hr,hc,hl,hperm,hcheck⟩

theorem recover_edges (S : Tree) (P : List (List Nat)) (o : Output)
    (ho : recover S P = some o) :
    o.sourceCuts.Nodup ∧ ∀ v, v ∈ o.sourceCuts → CoreGraph.Valid S v ∧ v ≠ [] := by
  have hr := (recover_sound S P o ho).1
  refine ⟨hr.1.1,?_⟩
  intro v hv
  exact ⟨hr.2.1 v hv,hr.1.2 v hv⟩

/-- The recovery wrapper succeeds exactly on its explicit ordinary source
checks. In particular a source-label partition alone cannot bypass embeddings. -/
theorem recover_success_iff (S : Tree) (P : List (List Nat)) :
    (∃ o, recover S P = some o) ↔ inputCheck S P = true := by
  constructor
  · rintro ⟨o,ho⟩
    exact (inputCheck_iff S P).2 (recover_some_guards S P o ho)
  · intro h
    obtain ⟨hn,hp,he⟩ := (inputCheck_iff S P).1 h
    obtain ⟨o,ho,_⟩ := recover_checked S P hn hp he
    exact ⟨o,ho⟩

/-- Recovery returns original source edges and preserves the agreement with
an arbitrary original target. This is a one-time final certificate extraction,
not a per-branch solver or a recurrence theorem. -/
theorem recover_original_agreement (T S : Tree) (P : List (List Nat))
    (hn : (leaves S).Nodup) (ha : agreement T S P = true) :
    ∃ o, recover S P = some o ∧ agreement T S o.partition = true ∧
      o.sourceCuts.length = P.length - 1 ∧ o.partition.length = P.length ∧
      CutRealization.RealizedOutput S o ∧ BlockPermutation P o.partition := by
  have hag := ha
  simp only [agreement,Bool.and_eq_true] at hag
  obtain ⟨o,ho,_,hc,hl,hr,hperm,_⟩ := recover_checked S P hn hag.1.1.1.2 hag.2
  exact ⟨o,ho,(agreement_block_permutation T S P o.partition hperm) ▸ ha,hc,hl,hr,hperm⟩

/-- Explicit accepted-input guard consequences for all original labels and
blocks. Missing/repeated/overlapping labels and empty blocks fail the literal
checker, while repeated source labels and embedding overlap have own guards. -/
theorem accepted_guards (S : Tree) (P : List (List Nat)) (o : Output)
    (ho : recover S P = some o) :
    (leaves S).Nodup ∧ P.flatten.Nodup ∧
    (∀ b, b ∈ P → b ≠ []) ∧
    (∀ x, x ∈ leaves S → P.flatten.count x = 1) ∧
    (∀ x, x ∈ P.flatten → x ∈ leaves S) ∧ pairwiseEmbeddings S P = true := by
  obtain ⟨hn,hp,he⟩ := recover_some_guards S P o ho
  refine ⟨hn,checked_flatten_nodup S P hp,partitionCheck_nonempty _ P hp,?_,?_,he⟩
  · intro x hx
    have hh : (leaves S).all (fun x => P.flatten.count x == 1) = true := by
      simp only [partitionCheck,Bool.and_eq_true] at hp
      exact hp.1.2
    exact beq_iff_eq.1 (List.all_eq_true.1 hh x hx)
  · intro x hx
    exact partitionCheck_subset _ P hp hx

end Universal233.FinalCutRecovery
