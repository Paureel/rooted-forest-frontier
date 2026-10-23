import OriginalColors

/-! Literal actual generator calls on the whole source and their raw output
lists. All hard2 cuts are charged by the original input color cardinality. -/
namespace Universal233.WholeSourceMass
open RMAF VertexGeometry SourceCoverage CoreProgram

structure WholeCall (S T : Tree) (A B C : List Nat) : Prop where
  partition : ParentPartition S A B C
  targetDistinct : (leaves T).Nodup
  sourceLabels : ∀ x, x ∈ leaves S → x ∈ leaves T
  aNonempty : A ≠ []
  bNonempty : B ≠ []
  cNonempty : C ≠ []

structure Occupied (D : List Nat) (T : Tree) (v : RMAF.Vertex) : Prop where
  nonlabel : ¬selectedLeaves D T v
  occupied : v ∈ minimalVertices D T

theorem WholeCall.colorA {S T A B C} (h : WholeCall S T A B C)
    (v : RMAF.Vertex) (hv : Occupied A T v) :
    2 ≤ (localColors A (colorLabel T v)).length :=
  original_colors_at_least_two A T v h.targetDistinct
    (partition_target_support S T A B C h.partition h.sourceLabels).1 hv.nonlabel hv.occupied

theorem WholeCall.colorB {S T A B C} (h : WholeCall S T A B C)
    (v : RMAF.Vertex) (hv : Occupied B T v) :
    2 ≤ (localColors B (colorLabel T v)).length :=
  original_colors_at_least_two B T v h.targetDistinct
    (partition_target_support S T A B C h.partition h.sourceLabels).2.1 hv.nonlabel hv.occupied

theorem WholeCall.colorC {S T A B C} (h : WholeCall S T A B C)
    (v : RMAF.Vertex) (hv : Occupied C T v) :
    2 ≤ (localColors C (colorLabel T v)).length :=
  original_colors_at_least_two C T v h.targetDistinct
    (partition_target_support S T A B C h.partition h.sourceLabels).2.2 hv.nonlabel hv.occupied

theorem negpow_antitone (b : Rat) (hb : 2 ≤ b) {m n : Nat} (hmn : m ≤ n) :
    b ^ (-(n : Int)) ≤ b ^ (-(m : Int)) := by
  have hbpos : 0 < b := by grind
  have hmpos : 0 < b ^ m := Rat.pow_pos hbpos
  have hnpos : 0 < b ^ n := Rat.pow_pos hbpos
  have hpow := qpow_mono b (by grind) hmn
  rw [Rat.zpow_neg,Rat.zpow_neg,Rat.zpow_natCast,Rat.zpow_natCast]
  apply Rat.le_of_mul_le_mul_left (c := b ^ n) _ hnpos
  rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt hnpos)]
  have hmul := Rat.mul_le_mul_of_nonneg_right hpow (Rat.le_of_lt (Rat.inv_pos.mpr hmpos))
  rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt hmpos)] at hmul
  exact hmul

theorem generate_mass_of_count (S : Tree) (color : Nat → Nat) (q L : Nat)
    (b : Rat) (hb : 2 ≤ b)
    (hr : L + 1 ≤ (dedupNat ((leaves S).map color)).length) :
    rawQMass b (generate S color q).outputs ≤ b ^ (-(L : Int)) := by
  let r := (dedupNat ((leaves S).map color)).length
  have hmass := generate_rawQ_mass S color q b hb
  have he : 1 - (r : Int) = -((r - 1 : Nat) : Int) := by dsimp [r]; omega
  change rawQMass b (generate S color q).outputs ≤ b ^ (1 - (r : Int)) at hmass
  rw [he] at hmass
  exact Rat.le_trans hmass (negpow_antitone b hb (by dsimp [r]; omega))

theorem rawQMass_append (b : Rat) (xs ys : List Output) :
    rawQMass b (xs ++ ys) = rawQMass b xs + rawQMass b ys := by
  simp [rawQMass,List.map_append,List.sum_append]

def wholeOutputs (S : Tree) (A B : List Nat) (ca cb cc : Nat → Nat) (q : Nat) : List Output :=
  (generate S (taggedColor A B ca cb cc) q).outputs

theorem wholeOutputs_mass (S : Tree) (A B C : List Nat)
    (hp : ParentPartition S A B C) (ca cb cc : Nat → Nat) (q L : Nat)
    (b : Rat) (hb : 2 ≤ b)
    (hr : L + 1 ≤ (localColors A ca).length + (localColors B cb).length +
      (localColors C cc).length) :
    rawQMass b (wholeOutputs S A B ca cb cc q) ≤ b ^ (-(L : Int)) := by
  apply generate_mass_of_count S (taggedColor A B ca cb cc) q L b hb
  rw [taggedColor_cardinality S A B C hp ca cb cc]
  exact hr

def cliqueOutputs (S T : Tree) (A B : List Nat) (v : RMAF.Vertex) (q : Nat) : List Output :=
  (wholeOutputs S A B (fun _ => 0) (colorLabel T v) (colorLabel T v) q ++
    wholeOutputs S A B (colorLabel T v) (fun _ => 0) (colorLabel T v) q) ++
    wholeOutputs S A B (colorLabel T v) (colorLabel T v) (fun _ => 0) q

/-- All three literal whole-source clique calls, including duplicate outputs. -/
theorem clique_raw_mass (S T : Tree) (A B C : List Nat)
    (h : WholeCall S T A B C) (v : RMAF.Vertex)
    (hA : Occupied A T v) (hB : Occupied B T v) (hC : Occupied C T v)
    (q : Nat) (b : Rat) (hb : 2 ≤ b) :
    rawQMass b (cliqueOutputs S T A B v q) ≤ 3 * b ^ (-4 : Int) := by
  have hca := h.colorA v hA
  have hcb := h.colorB v hB
  have hcc := h.colorC v hC
  have hza := localColors_zero A h.aNonempty
  have hzb := localColors_zero B h.bNonempty
  have hzc := localColors_zero C h.cNonempty
  have h1 := wholeOutputs_mass S A B C h.partition (fun _ => 0)
    (colorLabel T v) (colorLabel T v) q 4 b hb (by omega)
  have h2 := wholeOutputs_mass S A B C h.partition (colorLabel T v)
    (fun _ => 0) (colorLabel T v) q 4 b hb (by omega)
  have h3 := wholeOutputs_mass S A B C h.partition (colorLabel T v)
    (colorLabel T v) (fun _ => 0) q 4 b hb (by omega)
  simp only [cliqueOutputs,rawQMass_append]
  grind

def fourChainOutputs (S T : Tree) (A B : List Nat) (v w : RMAF.Vertex) (q : Nat) : List Output :=
  ((wholeOutputs S A B (fun _ => 0) (colorLabel T v) (colorLabel T w) q ++
    wholeOutputs S A B (fun _ => 0) (jointLabel T v w) (fun _ => 0) q) ++
    wholeOutputs S A B (colorLabel T v) (fun _ => 0) (colorLabel T w) q) ++
    wholeOutputs S A B (colorLabel T v) (colorLabel T w) (fun _ => 0) q

/-- The four chain calls use one joint middle generator, never a product of
independent same-parent cut sets. The geometric gate counts actual joint regions. -/
theorem four_chain_raw_mass (S T : Tree) (A B C : List Nat)
    (h : WholeCall S T A B C) (v w : RMAF.Vertex)
    (hA : Occupied A T v) (hBv : Occupied B T v)
    (hBw : Occupied B T w) (hC : Occupied C T w)
    (hj : 3 ≤ (jointColors B T v w).length)
    (q : Nat) (b : Rat) (hb : 2 ≤ b) :
    rawQMass b (fourChainOutputs S T A B v w q) ≤ 4 * b ^ (-4 : Int) := by
  have hca := h.colorA v hA
  have hcbv := h.colorB v hBv
  have hcbw := h.colorB w hBw
  have hcc := h.colorC w hC
  have hza := localColors_zero A h.aNonempty
  have hzb := localColors_zero B h.bNonempty
  have hzc := localColors_zero C h.cNonempty
  have hjc := original_joint_cardinality B T v w h.targetDistinct
    (partition_target_support S T A B C h.partition h.sourceLabels).2.1
  have h1 := wholeOutputs_mass S A B C h.partition (fun _ => 0)
    (colorLabel T v) (colorLabel T w) q 4 b hb (by omega)
  have h2 := wholeOutputs_mass S A B C h.partition (fun _ => 0)
    (jointLabel T v w) (fun _ => 0) q 4 b hb (by omega)
  have h3 := wholeOutputs_mass S A B C h.partition (colorLabel T v)
    (fun _ => 0) (colorLabel T w) q 4 b hb (by omega)
  have h4 := wholeOutputs_mass S A B C h.partition (colorLabel T v)
    (colorLabel T w) (fun _ => 0) q 4 b hb (by omega)
  simp only [fourChainOutputs,rawQMass_append]
  grind

def diagonalOutputs (S T : Tree) (A B : List Nat) (v w : RMAF.Vertex) (q : Nat) : List Output :=
  wholeOutputs S A B (fun _ => 0) (jointLabel T v w) (fun _ => 0) q ++
    wholeOutputs S A B (colorLabel T v) (fun _ => 0) (colorLabel T w) q

/-- Actual paid count-two diagonal: middle joint clearing versus both outer
parents, with every recorded source cut already charged. -/
theorem diagonal_raw_mass (S T : Tree) (A B C : List Nat)
    (h : WholeCall S T A B C) (v w : RMAF.Vertex)
    (hA : Occupied A T v) (hC : Occupied C T w)
    (hj : (jointColors B T v w).length = 2)
    (q : Nat) (b : Rat) (hb : 2 ≤ b) :
    rawQMass b (diagonalOutputs S T A B v w q) ≤ b ^ (-3 : Int) + b ^ (-4 : Int) := by
  have hca := h.colorA v hA
  have hcc := h.colorC w hC
  have hza := localColors_zero A h.aNonempty
  have hzb := localColors_zero B h.bNonempty
  have hzc := localColors_zero C h.cNonempty
  have hjc := original_joint_cardinality B T v w h.targetDistinct
    (partition_target_support S T A B C h.partition h.sourceLabels).2.1
  have h1 := wholeOutputs_mass S A B C h.partition (fun _ => 0)
    (jointLabel T v w) (fun _ => 0) q 3 b hb (by omega)
  have h2 := wholeOutputs_mass S A B C h.partition (colorLabel T v)
    (fun _ => 0) (colorLabel T w) q 4 b hb (by omega)
  simp only [diagonalOutputs,rawQMass_append]
  exact qadd_le_add h1 h2

end Universal233.WholeSourceMass
