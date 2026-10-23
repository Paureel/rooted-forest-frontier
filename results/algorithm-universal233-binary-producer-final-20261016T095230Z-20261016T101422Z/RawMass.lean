import ColorSteps

/-! One-shot raw output-list mass for actual run. We use a denominator-cleared
natural form, so duplicate list entries contribute separately to map/sum.
For b>=2, division by b^q b^(r-1) gives sum b^(-cost)<=b^(1-r).
The rational/real c>=2 transfer follows termwise from the b=2 result and the
separately proved all-emission cost>=r-1; it is documented in RESULT.md. -/
namespace Universal233.SourceCoverage
open RMAF CoreProgram CoreGraph Integration

def scaledMass (b offset : Nat) (outputs : List Output) : Nat :=
  (outputs.map (fun o => b ^ (offset - o.sourceCuts.length))).sum

@[simp] theorem scaledMass_nil (b offset : Nat) : scaledMass b offset [] = 0 := rfl

theorem scaledMass_append (b offset : Nat) (xs ys : List Output) :
    scaledMass b offset (xs ++ ys) = scaledMass b offset xs + scaledMass b offset ys := by
  simp [scaledMass,List.map_append,List.sum_append]

theorem attempt_scaled_mass (b q delta : Nat) (hb : 2 ≤ b)
    (ih : ∀ t d c, (origins t).Nodup →
      scaledMass b (q + c.length) (run q t d c).outputs * b ^ (colorCount t - 1) ≤ b ^ q)
    (t d c g) (hn : (origins t).Nodup) (v : RMAF.Vertex)
    (hv : GroupLeafAt t v g) (hvr : v ≠ [])
    (hr : ∀ u, GLeafErase t u v g → colorCount t - 1 ≤ (colorCount u - 1) + delta) :
    scaledMass b (q + 1 + c.length) (attempt (run q) t d c g).outputs *
      b ^ (colorCount t - 1) ≤ b ^ (q + delta) := by
  unfold attempt
  split
  · simp
  · split
    · simp
    · split
      · simp
      · rename_i u hu
        obtain ⟨u',hu',⟨herase⟩⟩ := erase_leaf_realization t hn v g hv hvr
        have he : u' = u := Option.some.inj (hu'.symm.trans hu)
        subst u'
        have hchild := ih u (g :: d) (g.origin :: c) (erase_origins_nodup t _ u hu hn)
        have hoffset : q + (g.origin :: c).length = q + 1 + c.length := by simp only [List.length_cons]; omega
        rw [hoffset] at hchild
        have hpow : b ^ (colorCount t - 1) ≤ b ^ ((colorCount u - 1) + delta) :=
          Nat.pow_le_pow_of_le (by omega) (hr u herase)
        change scaledMass b (q + 1 + c.length) (run q u (g :: d) (g.origin :: c)).outputs *
          b ^ (colorCount t - 1) ≤ b ^ (q + delta)
        calc
          _ ≤ scaledMass b (q + 1 + c.length) (run q u (g :: d) (g.origin :: c)).outputs *
              b ^ ((colorCount u - 1) + delta) := Nat.mul_le_mul_left _ hpow
          _ = (scaledMass b (q + 1 + c.length) (run q u (g :: d) (g.origin :: c)).outputs *
              b ^ (colorCount u - 1)) * b ^ delta := by rw [Nat.pow_add,Nat.mul_assoc]
          _ ≤ b ^ q * b ^ delta := Nat.mul_le_mul_right _ hchild
          _ = b ^ (q + delta) := (Nat.pow_add _ _ _).symm

theorem finish_colorCount (t : GTree) (hc : choose t = .finish) : colorCount t = 1 := by
  obtain ⟨i,hi⟩ := choose_finish_cover t hc
  have hle := colorCount_le_cover t [i] hi
  have hpos := colorCount_pos t
  simp only [List.length_singleton] at hle
  omega

theorem pruned_attempt_outputs (t d c g) :
    (attempt (fun _ _ _ => (⟨[],[],0,0,1⟩ : Receipt)) t d c g).outputs = [] := by
  unfold attempt
  split <;> first | rfl | (split <;> first | rfl | (split <;> rfl))

/-- Universal raw emitted-list mass, in an exact denominator-cleared form.
No output deduplication is performed or assumed. Every refused or pruned branch
contributes its actual empty output list. -/
theorem run_scaled_mass (b : Nat) (hb : 2 ≤ b) (q : Nat) (t d c)
    (hn : (origins t).Nodup) :
    scaledMass b (q + c.length) (run q t d c).outputs * b ^ (colorCount t - 1) ≤ b ^ q := by
  induction q generalizing t d c with
  | zero =>
    cases hc : choose (normalize t) with
    | finish =>
      have hr : colorCount t = 1 := (colorCount_normalize t).symm.trans (finish_colorCount _ hc)
      simp [run,step,hc,scaledMass,hr]
    | one g => simp [run,step,hc,prefixRoot,pruned_attempt_outputs]
    | two a b => simp [run,step,hc,prefixRoot,combine,pruned_attempt_outputs]
    | refuse why => simp [run,step,hc]
  | succ q ih =>
    have hnn := normalize_origins_nodup t hn
    have hrank := colorCount_normalize t
    cases hc : choose (normalize t) with
    | finish =>
      have hr : colorCount t = 1 := hrank.symm.trans (finish_colorCount _ hc)
      simp [run,step,hc,scaledMass,hr]
    | one g =>
      obtain ⟨hg,hfilter⟩ := choose_one_selected (normalize t) g hc
      obtain ⟨v,hv⟩ := groupLeaf_of_groups_mem (normalize t) g hg
      have hvr := choose_one_nonroot (normalize t) g hc v hv
      have ha := attempt_scaled_mass b q 1 hb (by intros; apply ih; assumption)
        (normalize t) d c g hnn v hv hvr (by
          intro u hu
          have hcol := erase_colorCount_one hu
          have hpos := colorCount_pos u
          omega)
      simpa only [run,step,hc,prefixRoot,hrank] using ha
    | two a z =>
      obtain ⟨p,hp,hne⟩ := choose_two_selected (normalize t) a z hc
      have ha := attempt_scaled_mass b q 0 hb (by intros; apply ih; assumption)
        (normalize t) d c a hnn (p ++ [false]) (gcherry_left hp) (by simp) (by
          intro u hu
          have hcol := erase_colorCount_two hu hnn
            (choose_two_nonunique (normalize t) a z a hc (groupLeaf_mem_groups _ _ _ (gcherry_left hp)))
          omega)
      have hz := attempt_scaled_mass b q 0 hb (by intros; apply ih; assumption)
        (normalize t) d c z hnn (p ++ [true]) (gcherry_right hp) (by simp) (by
          intro u hu
          have hcol := erase_colorCount_two hu hnn
            (choose_two_nonunique (normalize t) a z z hc (groupLeaf_mem_groups _ _ _ (gcherry_right hp)))
          omega)
      simp only [Nat.add_zero,hrank] at ha hz
      have hsum := Nat.add_le_add ha hz
      have htwo : b ^ q + b ^ q ≤ b ^ (q + 1) := by
        rw [Nat.pow_succ]
        have hh := Nat.mul_le_mul_left (b ^ q) hb
        omega
      simp only [run,step,hc,prefixRoot,combine,scaledMass_append,Nat.add_mul]
      exact Nat.le_trans hsum htwo
    | refuse why => simp [run,step,hc]

/-- Exact raw mass for every actual generate emission, including duplicate
entries, with the cap used by generate itself. -/
theorem generate_scaled_mass (t : Tree) (color : Nat → Nat) (q b : Nat) (hb : 2 ≤ b) :
    scaledMass b (min q ((leaves t).length - 1)) (generate t color q).outputs *
      b ^ ((dedupNat ((leaves t).map color)).length - 1) ≤
      b ^ (min q ((leaves t).length - 1)) := by
  unfold generate
  split
  · have hm := run_scaled_mass b hb (min q ((leaves t).length - 1))
      (fromTree color [] t) [] [] (fromTree_origins_nodup color [] t)
    simpa only [List.length_nil,Nat.add_zero,colorCount,fromTree_colors] using hm
  · simp

end Universal233.SourceCoverage
