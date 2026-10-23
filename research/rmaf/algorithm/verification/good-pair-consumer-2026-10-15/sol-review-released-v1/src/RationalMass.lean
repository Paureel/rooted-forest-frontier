import RawMass

/-! One-shot rational raw output-list mass for actual run/generate. Duplicate
list entries contribute separately. The cleared inequality is converted to the
literal negative-power sum using the proved actual output cap. -/
namespace Universal233.SourceCoverage
open RMAF CoreProgram CoreGraph Integration

def scaledQMass (b : Rat) (offset : Nat) (outputs : List Output) : Rat :=
  (outputs.map (fun o => b ^ (offset - o.sourceCuts.length))).sum

theorem qpow_add (b : Rat) (m n : Nat) : b ^ (m + n) = b ^ m * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.add_succ,Rat.pow_succ,ih,Rat.mul_assoc]

theorem qpow_mono (b : Rat) (hb : 1 ≤ b) {m n : Nat} (h : m ≤ n) : b ^ m ≤ b ^ n := by
  induction n generalizing m with
  | zero => have he : m = 0 := by omega
            simp [he]
  | succ n ih =>
    by_cases he : m = n + 1
    · simp [he]
    · have hmn : m ≤ n := by omega
      have hprev := ih hmn
      have hstep := Rat.mul_le_mul_of_nonneg_left hb (Rat.pow_nonneg (a := b) (n := n) (by grind))
      rw [Rat.mul_one] at hstep
      exact Rat.le_trans hprev (by simpa only [Rat.pow_succ] using hstep)

theorem qadd_le_add {a b c d : Rat} (h : a ≤ b) (k : c ≤ d) : a + c ≤ b + d := by grind

theorem scaledQMass_nonneg (b : Rat) (hb : 0 ≤ b) (offset : Nat) (outputs : List Output) :
    0 ≤ scaledQMass b offset outputs := by
  induction outputs with
  | nil => simp [scaledQMass]
  | cons o os ih =>
    have hp := Rat.pow_nonneg (a := b) (n := offset - o.sourceCuts.length) hb
    simpa only [scaledQMass,List.map_cons,List.sum_cons] using Rat.add_nonneg hp ih

@[simp] theorem scaledQMass_nil (b : Rat) (offset : Nat) : scaledQMass b offset [] = 0 := rfl

theorem scaledQMass_append (b : Rat) (offset : Nat) (xs ys : List Output) :
    scaledQMass b offset (xs ++ ys) = scaledQMass b offset xs + scaledQMass b offset ys := by
  simp [scaledQMass,List.map_append,List.sum_append]

theorem attempt_scaledQ_mass (b : Rat) (q delta : Nat) (hb : 2 ≤ b)
    (ih : ∀ t d c, (origins t).Nodup →
      scaledQMass b (q + c.length) (run q t d c).outputs * b ^ (colorCount t - 1) ≤ b ^ q)
    (t d c g) (hn : (origins t).Nodup) (v : RMAF.Vertex)
    (hv : GroupLeafAt t v g) (hvr : v ≠ [])
    (hr : ∀ u, GLeafErase t u v g → colorCount t - 1 ≤ (colorCount u - 1) + delta) :
    scaledQMass b (q + 1 + c.length) (attempt (run q) t d c g).outputs *
      b ^ (colorCount t - 1) ≤ b ^ (q + delta) := by
  unfold attempt
  split
  · simp; exact Rat.pow_nonneg (by grind)
  · split
    · simp; exact Rat.pow_nonneg (by grind)
    · split
      · simp; exact Rat.pow_nonneg (by grind)
      · rename_i u hu
        obtain ⟨u',hu',⟨herase⟩⟩ := erase_leaf_realization t hn v g hv hvr
        have he : u' = u := Option.some.inj (hu'.symm.trans hu)
        subst u'
        have hchild := ih u (g :: d) (g.origin :: c) (erase_origins_nodup t _ u hu hn)
        have hoffset : q + (g.origin :: c).length = q + 1 + c.length := by simp only [List.length_cons]; omega
        rw [hoffset] at hchild
        have hpow : b ^ (colorCount t - 1) ≤ b ^ ((colorCount u - 1) + delta) :=
          qpow_mono b (by grind) (hr u herase)
        change scaledQMass b (q + 1 + c.length) (run q u (g :: d) (g.origin :: c)).outputs *
          b ^ (colorCount t - 1) ≤ b ^ (q + delta)
        calc
          _ ≤ scaledQMass b (q + 1 + c.length) (run q u (g :: d) (g.origin :: c)).outputs *
              b ^ ((colorCount u - 1) + delta) := Rat.mul_le_mul_of_nonneg_left hpow (scaledQMass_nonneg b (by grind) _ _)
          _ = (scaledQMass b (q + 1 + c.length) (run q u (g :: d) (g.origin :: c)).outputs *
              b ^ (colorCount u - 1)) * b ^ delta := by rw [qpow_add,Rat.mul_assoc]
          _ ≤ b ^ q * b ^ delta := Rat.mul_le_mul_of_nonneg_right hchild (Rat.pow_nonneg (by grind))
          _ = b ^ (q + delta) := (qpow_add _ _ _).symm

/-- Universal raw emitted-list mass, in an exact denominator-cleared form.
No output deduplication is performed or assumed. Every refused or pruned branch
contributes its actual empty output list. -/
theorem run_scaledQ_mass (b : Rat) (hb : 2 ≤ b) (q : Nat) (t d c)
    (hn : (origins t).Nodup) :
    scaledQMass b (q + c.length) (run q t d c).outputs * b ^ (colorCount t - 1) ≤ b ^ q := by
  induction q generalizing t d c with
  | zero =>
    cases hc : choose (normalize t) with
    | finish =>
      have hr : colorCount t = 1 := (colorCount_normalize t).symm.trans (finish_colorCount _ hc)
      simp [run,step,hc,scaledQMass,hr]; grind
    | one g => simp [run,step,hc,prefixRoot,pruned_attempt_outputs]; grind
    | two a b => simp [run,step,hc,prefixRoot,combine,pruned_attempt_outputs]; grind
    | refuse why => simp [run,step,hc]; grind
  | succ q ih =>
    have hnn := normalize_origins_nodup t hn
    have hrank := colorCount_normalize t
    cases hc : choose (normalize t) with
    | finish =>
      have hr : colorCount t = 1 := hrank.symm.trans (finish_colorCount _ hc)
      simp [run,step,hc,scaledQMass,hr]; grind
    | one g =>
      obtain ⟨hg,hfilter⟩ := choose_one_selected (normalize t) g hc
      obtain ⟨v,hv⟩ := groupLeaf_of_groups_mem (normalize t) g hg
      have hvr := choose_one_nonroot (normalize t) g hc v hv
      have ha := attempt_scaledQ_mass b q 1 hb (by intros; apply ih; assumption)
        (normalize t) d c g hnn v hv hvr (by
          intro u hu
          have hcol := erase_colorCount_one hu
          have hpos := colorCount_pos u
          omega)
      simpa only [run,step,hc,prefixRoot,hrank] using ha
    | two a z =>
      obtain ⟨p,hp,hne⟩ := choose_two_selected (normalize t) a z hc
      have ha := attempt_scaledQ_mass b q 0 hb (by intros; apply ih; assumption)
        (normalize t) d c a hnn (p ++ [false]) (gcherry_left hp) (by simp) (by
          intro u hu
          have hcol := erase_colorCount_two hu hnn
            (choose_two_nonunique (normalize t) a z a hc (groupLeaf_mem_groups _ _ _ (gcherry_left hp)))
          omega)
      have hz := attempt_scaledQ_mass b q 0 hb (by intros; apply ih; assumption)
        (normalize t) d c z hnn (p ++ [true]) (gcherry_right hp) (by simp) (by
          intro u hu
          have hcol := erase_colorCount_two hu hnn
            (choose_two_nonunique (normalize t) a z z hc (groupLeaf_mem_groups _ _ _ (gcherry_right hp)))
          omega)
      simp only [Nat.add_zero,hrank] at ha hz
      have hsum := qadd_le_add ha hz
      have htwo : b ^ q + b ^ q ≤ b ^ (q + 1) := by
        rw [Rat.pow_succ]
        have hh := Rat.mul_le_mul_of_nonneg_left hb (Rat.pow_nonneg (a := b) (n := q) (by grind))
        grind
      simp only [run,step,hc,prefixRoot,combine,scaledQMass_append,Rat.add_mul]
      exact Rat.le_trans hsum htwo
    | refuse why => simp [run,step,hc]; exact Rat.pow_nonneg (by grind)

/-- Exact raw mass for every actual generate emission, including duplicate
entries, with the cap used by generate itself. -/
theorem generate_scaledQ_mass (t : Tree) (color : Nat → Nat) (q : Nat) (b : Rat) (hb : 2 ≤ b) :
    scaledQMass b (min q ((leaves t).length - 1)) (generate t color q).outputs *
      b ^ ((dedupNat ((leaves t).map color)).length - 1) ≤
      b ^ (min q ((leaves t).length - 1)) := by
  unfold generate
  split
  · have hm := run_scaledQ_mass b hb (min q ((leaves t).length - 1))
      (fromTree color [] t) [] [] (fromTree_origins_nodup color [] t)
    simpa only [List.length_nil,Nat.add_zero,colorCount,fromTree_colors] using hm
  · simp; exact Rat.pow_nonneg (by grind)

def rawQMass (b : Rat) (outputs : List Output) : Rat :=
  (outputs.map (fun o => b ^ (-(o.sourceCuts.length : Int)))).sum

theorem qpow_clear (b : Rat) (hb : b ≠ 0) (B d : Nat) (hd : d ≤ B) :
    b ^ (B - d) = b ^ B * b ^ (-(d : Int)) := by
  have hexp : ((B - d : Nat) : Int) = (B : Int) + -(d : Int) := by omega
  calc
    _ = b ^ (((B - d : Nat) : Int)) := rfl
    _ = b ^ ((B : Int) + -(d : Int)) := congrArg (fun e : Int => b ^ e) hexp
    _ = b ^ (B : Int) * b ^ (-(d : Int)) := Rat.zpow_add hb _ _
    _ = b ^ B * b ^ (-(d : Int)) := rfl

theorem scaledQMass_clear (b : Rat) (hb : b ≠ 0) (B : Nat) (outputs : List Output)
    (hbound : ∀ o, o ∈ outputs → o.sourceCuts.length ≤ B) :
    scaledQMass b B outputs = b ^ B * rawQMass b outputs := by
  induction outputs with
  | nil => simp [scaledQMass,rawQMass]
  | cons o os ih =>
    have hd := hbound o (by simp)
    have ihr := ih (by intro a ha; exact hbound a (List.mem_cons_of_mem o ha))
    change b ^ (B - o.sourceCuts.length) + scaledQMass b B os =
      b ^ B * (b ^ (-(o.sourceCuts.length : Int)) + rawQMass b os)
    rw [qpow_clear b hb B _ hd,ihr,Rat.mul_add]

theorem generate_output_cap (t : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate t color q).outputs) :
    o.sourceCuts.length ≤ min q ((leaves t).length - 1) := by
  unfold generate at ho
  split at ho
  · have h := run_output_budget _ _ _ _ o ho
    simpa only [List.length_nil,Nat.zero_add] using h
  · simp at ho

/-- Universal raw output-list mass at every rational base c>=2, including
c=233/100. The sum includes every duplicate entry and uses actual recorded
cut counts. Original cut-component realization is a separate assertion. -/
theorem generate_rawQ_mass (t : Tree) (color : Nat → Nat) (q : Nat)
    (b : Rat) (hb : 2 ≤ b) :
    rawQMass b (generate t color q).outputs ≤
      b ^ (1 - ((dedupNat ((leaves t).map color)).length : Int)) := by
  let B := min q ((leaves t).length - 1)
  let r := (dedupNat ((leaves t).map color)).length
  have hbpos : 0 < b := by grind
  have hbne : b ≠ 0 := Rat.ne_of_gt hbpos
  have hmass := generate_scaledQ_mass t color q b hb
  have hclear := scaledQMass_clear b hbne B (generate t color q).outputs
    (generate_output_cap t color q)
  change scaledQMass b B (generate t color q).outputs * b ^ (r - 1) ≤ b ^ B at hmass
  rw [hclear] at hmass
  have hmid : rawQMass b (generate t color q).outputs * b ^ (r - 1) ≤ 1 := by
    apply Rat.le_of_mul_le_mul_left (c := b ^ B) _ (Rat.pow_pos hbpos)
    simpa only [Rat.mul_assoc,Rat.mul_one] using hmass
  have hrpos : 0 < r := by
    have h := colorCount_pos (fromTree color [] t)
    simpa only [colorCount,fromTree_colors,r] using h
  have hprpos : 0 < b ^ (r - 1) := Rat.pow_pos hbpos
  apply Rat.le_of_mul_le_mul_right (c := b ^ (r - 1)) _ hprpos
  have hexp : 1 - (r : Int) = -((r - 1 : Nat) : Int) := by omega
  change rawQMass b (generate t color q).outputs * b ^ (r - 1) ≤
    b ^ (1 - (r : Int)) * b ^ (r - 1)
  rw [hexp,Rat.zpow_neg,Rat.zpow_natCast,Rat.inv_mul_cancel _ (Rat.ne_of_gt hprpos)]
  exact hmid

end Universal233.SourceCoverage
