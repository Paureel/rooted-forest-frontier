import RankCost

namespace Universal233.RankDichotomy
open RMAF CoreProgram SourceCoverage VertexGeometry

theorem attempt_outputs_mono (f g : GTree → List Group → List RMAF.Vertex → Receipt)
    (h : ∀ t d c o, o ∈ (f t d c).outputs → o ∈ (g t d c).outputs)
    (t d c a o) (ho : o ∈ (attempt f t d c a).outputs) :
    o ∈ (attempt g t d c a).outputs := by
  by_cases hr : a.origin = []
  · simp [attempt,hr] at ho
  · by_cases hd : a.origin ∈ c
    · simp [attempt,hr,hd] at ho
    · cases he : erase a.origin t with
      | none => simp [attempt,hr,hd,he] at ho
      | some next =>
          have hh : o ∈ (f next (a :: d) (a.origin :: c)).outputs := by
            simpa [attempt,hr,hd,he] using ho
          simpa [attempt,hr,hd,he] using h next (a :: d) (a.origin :: c) o hh

theorem step_outputs_mono (f g : GTree → List Group → List RMAF.Vertex → Receipt)
    (h : ∀ t d c o, o ∈ (f t d c).outputs → o ∈ (g t d c).outputs)
    (t d c o) (ho : o ∈ (step f t d c).outputs) : o ∈ (step g t d c).outputs := by
  cases hc : choose (normalize t) with
  | finish => simpa [step,hc] using ho
  | one a =>
      have hh := attempt_outputs_mono f g h _ _ _ a o (by simpa [step,hc,prefixRoot] using ho)
      simpa [step,hc,prefixRoot] using hh
  | two a b =>
      have hm : o ∈ (attempt f (normalize t) d c a).outputs ∨
          o ∈ (attempt f (normalize t) d c b).outputs := by simpa [step,hc,prefixRoot,combine] using ho
      have hm' : o ∈ (attempt g (normalize t) d c a).outputs ∨
          o ∈ (attempt g (normalize t) d c b).outputs := by
        rcases hm with ha | hb
        · exact Or.inl (attempt_outputs_mono f g h _ _ _ a o ha)
        · exact Or.inr (attempt_outputs_mono f g h _ _ _ b o hb)
      simpa [step,hc,prefixRoot,combine] using hm'
  | refuse why => simp [step,hc] at ho

theorem run_outputs_succ (q : Nat) (t d c o) (ho : o ∈ (run q t d c).outputs) :
    o ∈ (run (q+1) t d c).outputs := by
  induction q generalizing t d c o with
  | zero =>
      exact step_outputs_mono _ (run 0) (by intros; contradiction) t d c o ho
  | succ q ih => exact step_outputs_mono (run q) (run (q+1)) ih t d c o ho

theorem run_outputs_mono {q q' : Nat} (hq : q ≤ q') (t d c o)
    (ho : o ∈ (run q t d c).outputs) : o ∈ (run q' t d c).outputs := by
  induction hq with
  | refl => exact ho
  | @step n hn ih => exact run_outputs_succ n t d c o ih

theorem generate_outputs_mono (T : Tree) (color : Nat → Nat) {q q' : Nat}
    (hq : q ≤ q') (o : Output) (ho : o ∈ (generate T color q).outputs) :
    o ∈ (generate T color q').outputs := by
  unfold generate at ho ⊢
  split <;> first | simp_all | skip
  apply run_outputs_mono (q := min q ((leaves T).length - 1))
    (by omega) _ _ _ _ ho

theorem rawQMass_nonneg (b : Rat) (hb : 0 < b) (xs : List Output) : 0 ≤ rawQMass b xs := by
  induction xs with
  | nil => simp [rawQMass]
  | cons a xs ih =>
      have ha : 0 < b ^ (-(a.sourceCuts.length : Int)) := Rat.zpow_pos hb
      change 0 ≤ b ^ (-(a.sourceCuts.length : Int)) + rawQMass b xs
      grind

theorem rawQMass_positive (b : Rat) (hb : 0 < b) (a : Output) (xs : List Output) :
    0 < rawQMass b (a :: xs) := by
  have ha : 0 < b ^ (-(a.sourceCuts.length : Int)) := Rat.zpow_pos hb
  have hs := rawQMass_nonneg b hb xs
  change 0 < b ^ (-(a.sourceCuts.length : Int)) + rawQMass b xs
  grind

/-- Saturation excludes every other literal list entry, including duplicates. -/
theorem rawQMass_saturated (b : Rat) (hb : 0 < b) (xs : List Output) (o : Output)
    (ho : o ∈ xs) (hm : rawQMass b xs ≤ b ^ (-(o.sourceCuts.length : Int))) : xs = [o] := by
  induction xs with
  | nil => simp at ho
  | cons a xs ih =>
      have ha : 0 < b ^ (-(a.sourceCuts.length : Int)) := Rat.zpow_pos hb
      have hs := rawQMass_nonneg b hb xs
      change b ^ (-(a.sourceCuts.length : Int)) + rawQMass b xs ≤ _ at hm
      rcases List.mem_cons.mp ho with he | ho
      · subst a
        cases xs with
        | nil => rfl
        | cons z zs => have hp := rawQMass_positive b hb z zs; grind
      · have hrest : rawQMass b xs ≤ b ^ (-(o.sourceCuts.length : Int)) := by grind
        have he := ih ho hrest
        subst xs
        change b ^ (-(a.sourceCuts.length : Int)) +
          (b ^ (-(o.sourceCuts.length : Int)) + 0) ≤ b ^ (-(o.sourceCuts.length : Int)) at hm
        grind

/-- Source-valid rank feasibility yields the literal unique output at every
sufficient budget. This route uses source coverage plus actual Kraft saturation,
so there is no assumed deterministic grammar or confluence hypothesis. -/
theorem feasible_unique (T : Tree) (color : Nat → Nat) (hn : (leaves T).Nodup)
    (hf : RankFeasible T color) (q : Nat) (hq : inputRank T color - 1 ≤ q) :
    ∃ o, (generate T color q).outputs = [o] ∧ o.sourceCuts.length = inputRank T color - 1 := by
  obtain ⟨bs,hp,he,hm,hlen⟩ := hf
  obtain ⟨o,ho,href,hcost⟩ := generate_partition_coverage_paid T bs color hn hp he hm
    (inputRank T color - 1) (by omega)
  have hlo := generate_color_cost T color (inputRank T color - 1) o ho
  have hr := inputRank_pos T color
  change inputRank T color ≤ o.sourceCuts.length + 1 at hlo
  have hpaid : o.sourceCuts.length = inputRank T color - 1 := by omega
  have hoq := generate_outputs_mono T color hq o ho
  have hmass := generate_rawQ_mass T color q 2 (by decide)
  have hexp : 1 - (inputRank T color : Int) = -(o.sourceCuts.length : Int) := by omega
  change rawQMass 2 (generate T color q).outputs ≤ 2 ^ (1 - (inputRank T color : Int)) at hmass
  rw [hexp] at hmass
  exact ⟨o,rawQMass_saturated 2 (by decide) _ o hoq hmass,hpaid⟩

end Universal233.RankDichotomy
