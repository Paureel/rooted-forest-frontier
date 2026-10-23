import Recovery
import Work

/-! Source-operation accounting wrapper. The core's reviewed helper-to-fine
operation qualification is retained; scalar bit costs are stated separately in
COST-MODEL.md. The explicit finite block-color scan is no longer an arbitrary
oracle, and only head? is used after generate: no equivalence scan is hidden. -/
namespace Universal233.FinalCutRecovery
open RMAF CoreProgram CoreWork SourceCoverage VertexGeometry

/-- Conservative guard envelope in list/address operations, including both
literal partition checks and all source embeddings, also on refused input. -/
def guardCharge (S : Tree) (P : List (List Nat)) : Nat :=
  4096 * (treeNodes S + P.flatten.length + P.length + 2)^8

/-- Each color lookup scans at most every input block and every label cell.
The core evaluates the color only at the original leaves during fromTree. -/
def colorCharge (S : Tree) (P : List (List Nat)) : Nat :=
  32 * (leaves S).length * (P.flatten.length + P.length + 1)

structure ColorMeasured where
  value : Nat
  work : Nat
  deriving Repr

/-- The same literal contains guard and early stop as blockColor. The charge
covers the full visited block, hence also contains' earlier stop. -/
def meterColor : List (List Nat) → Nat → ColorMeasured
  | [], _ => ⟨0,1⟩
  | b :: P, x =>
    if b.contains x then ⟨b.headD 0,8*(b.length+1)+2⟩
    else let r := meterColor P x
         ⟨r.value,8*(b.length+1)+r.work+2⟩

theorem meterColor_value (P : List (List Nat)) (x : Nat) :
    (meterColor P x).value = blockColor P x := by
  induction P with
  | nil => rfl
  | cons b P ih => simp only [meterColor,blockColor]; split <;> simp_all

theorem meterColor_work (P : List (List Nat)) (x : Nat) :
    (meterColor P x).work ≤ 32*(P.flatten.length+P.length+1) := by
  induction P with
  | nil => simp [meterColor]
  | cons b P ih =>
    simp only [meterColor]
    split <;> simp only [List.flatten_cons,List.length_append,List.length_cons]
    · omega
    · omega

theorem total_color_work (P : List (List Nat)) (xs : List Nat) :
    (xs.map (fun x => (meterColor P x).work)).sum ≤
      32*xs.length*(P.flatten.length+P.length+1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := meterColor_work P x
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    have hh := Nat.add_le_add hx ih
    have he : 32*(P.flatten.length+P.length+1) +
        32*xs.length*(P.flatten.length+P.length+1) =
        32*(xs.length+1)*(P.flatten.length+P.length+1) := by
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
      omega
    exact he ▸ hh

structure RecoveryMeasured where
  value : Option Output
  work : Nat
  deriving Repr

def meterRecover (S : Tree) (P : List (List Nat)) : RecoveryMeasured :=
  if inputCheck S P then
    let g := meterGenerate S (blockColor P) (P.length - 1)
    ⟨g.measured.receipt.outputs.head?,guardCharge S P + g.measured.work + colorCharge S P + 1⟩
  else ⟨none,guardCharge S P⟩

theorem meterRecover_value (S : Tree) (P : List (List Nat)) :
    (meterRecover S P).value = recover S P := by
  simp only [meterRecover,recover,meterGenerate_receipt]
  split <;> rfl

theorem checked_flatten_perm (S : Tree) (P : List (List Nat))
    (hn : (leaves S).Nodup) (hp : partitionCheck (leaves S) P = true) :
    P.flatten.Perm (leaves S) := by
  apply List.perm_iff_count.2
  intro x
  by_cases hx : x ∈ leaves S
  · have hh : (leaves S).all (fun x => P.flatten.count x == 1) = true := by
      simp only [partitionCheck,Bool.and_eq_true] at hp
      exact hp.1.2
    rw [beq_iff_eq.1 (List.all_eq_true.1 hh x hx),List.nodup_iff_count_of_mem.1 hn x hx]
  · have hxP : x ∉ P.flatten := fun hxP => hx (partitionCheck_subset _ P hp hxP)
    rw [List.count_eq_zero_of_not_mem hxP,List.count_eq_zero_of_not_mem hx]

theorem blocks_le_flatten (P : List (List Nat)) (h : ∀ b, b ∈ P → b ≠ []) :
    P.length ≤ P.flatten.length := by
  induction P with
  | nil => simp
  | cons b P ih =>
    have hb : 1 ≤ b.length := by cases b <;> simp_all
    have hi := ih (fun c hc => h c (by simp [hc]))
    simp only [List.flatten_cons,List.length_append,List.length_cons]
    omega

/-- Complete final-output polynomial coefficient, in source/list operations.
On checked input P.flatten has n cells and 1 ≤ |P| ≤ n; this is polynomial in
n. No branch count or prefix is removed by final uniqueness. -/
def finalPolynomial (S : Tree) (P : List (List Nat)) : Nat :=
  (guardCharge S P + colorCharge S P + initialCharge S + 1) +
    2*(cap (inputResource S)+6)*P.length

/-- All visited, refused and budget-pruned prefixes and actual receipt append
work are paid by the imported complete core envelope. Coloring and the final
head? extraction are explicit additive bills. -/
theorem final_work_bound (S : Tree) (P : List (List Nat))
    (hn : (leaves S).Nodup) (hp : partitionCheck (leaves S) P = true)
    (he : pairwiseEmbeddings S P = true) :
    (meterRecover S P).work ≤ finalPolynomial S P * 2^(P.length - 1) := by
  have hflat := (checked_flatten_perm S P hn hp).length_eq
  have hcount := blocks_le_flatten P (partitionCheck_nonempty _ P hp)
  have hpos := RankDichotomy.inputRank_pos S (blockColor P)
  rw [checked_rank S P hp] at hpos
  have hcap : min (P.length - 1) ((leaves S).length - 1) = P.length - 1 := by omega
  have hguard := (inputCheck_iff S P).2 ⟨hn,hp,he⟩
  have hcore := generate_work_bound S (blockColor P) (P.length - 1)
  rw [hcap] at hcore
  have hfactor : (cap (inputResource S)+6)*(P.length - 1+1)*2^(P.length - 1+1) =
      (2*(cap (inputResource S)+6)*P.length)*2^(P.length - 1) := by
    have hlen : P.length - 1+1 = P.length := by omega
    rw [Nat.pow_succ,hlen]
    ac_rfl
  rw [hfactor] at hcore
  have hpw : 1 ≤ 2^(P.length - 1) := Nat.one_le_pow _ _ (by decide)
  have ha := Nat.mul_le_mul_left (guardCharge S P + colorCharge S P + initialCharge S + 1) hpw
  simp only [Nat.mul_one] at ha
  simp only [meterRecover,hguard,ite_true]
  unfold finalPolynomial
  rw [Nat.add_mul]
  omega

/-- The exponential is the returned certificate's actual original cut cost. -/
theorem final_work_actual_cost (S : Tree) (P : List (List Nat))
    (hn : (leaves S).Nodup) (hp : partitionCheck (leaves S) P = true)
    (he : pairwiseEmbeddings S P = true) :
    ∃ o, recover S P = some o ∧ CutRealization.RealizedOutput S o ∧
      o.sourceCuts.length = P.length - 1 ∧
      (meterRecover S P).work ≤ finalPolynomial S P * 2^o.sourceCuts.length := by
  obtain ⟨o,ho,_,hc,_,hr,_⟩ := recover_checked S P hn hp he
  exact ⟨o,ho,hr,hc,hc ▸ final_work_bound S P hn hp he⟩

/-- General rational-base absorption for the one final call. It is additive
in the caller's work; no search recurrence is asserted. -/
theorem qpow_base_mono (a b : Rat) (ha : 0 ≤ a) (hab : a ≤ b) (r : Nat) :
    a^r ≤ b^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 := Rat.mul_le_mul_of_nonneg_right ih ha
    have hb : 0 ≤ b := Rat.le_trans ha hab
    have h2 := Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg (a := b) (n := r) hb)
    exact Rat.le_trans (by simpa only [Rat.pow_succ] using h1)
      (by simpa only [Rat.pow_succ] using h2)

theorem final_work_absorbed (S : Tree) (P : List (List Nat))
    (hn : (leaves S).Nodup) (hp : partitionCheck (leaves S) P = true)
    (he : pairwiseEmbeddings S P = true) (q : Nat) (hq : P.length - 1 ≤ q)
    (c : Rat) (hc : 2 ≤ c) :
    ((meterRecover S P).work : Rat) ≤ (finalPolynomial S P : Rat)*c^q := by
  have hnat := Rat.natCast_le_natCast.2 (final_work_bound S P hn hp he)
  rw [Rat.natCast_mul,Rat.natCast_pow] at hnat
  have hbase := qpow_base_mono 2 c (by decide) hc (P.length - 1)
  have hexp := SourceCoverage.qpow_mono c (by grind) hq
  have hpow := Rat.le_trans hbase hexp
  have hpoly : 0 ≤ (finalPolynomial S P : Rat) := Rat.natCast_le_natCast.2 (Nat.zero_le _)
  exact Rat.le_trans hnat (Rat.mul_le_mul_of_nonneg_left hpow hpoly)

end Universal233.FinalCutRecovery
