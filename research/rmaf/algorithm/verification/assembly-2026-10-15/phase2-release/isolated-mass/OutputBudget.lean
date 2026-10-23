import Entrypoint

/-! One-shot syntactic budget bounds for every actual emitted list member. -/
namespace Universal233.SourceCoverage
open RMAF CoreProgram CoreGraph Integration VertexGeometry

theorem attempt_budget (n : Nat) (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (h : ∀ t d c o, o ∈ (f t d c).outputs → o.sourceCuts.length ≤ c.length + n)
    (t d c g o) (ho : o ∈ (attempt f t d c g).outputs) :
    o.sourceCuts.length ≤ c.length + (n + 1) := by
  unfold attempt at ho
  split at ho
  · simp at ho
  · split at ho
    · simp at ho
    · split at ho
      · simp at ho
      · have hb := h _ _ _ o ho
        simp only [List.length_cons] at hb
        omega

theorem step_budget (n : Nat) (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (h : ∀ t d c o, o ∈ (f t d c).outputs → o.sourceCuts.length ≤ c.length + n)
    (t d c o) (ho : o ∈ (step f t d c).outputs) :
    o.sourceCuts.length ≤ c.length + (n + 1) := by
  cases hc : choose (normalize t) with
  | finish => have he : o = ⟨d.map Group.labels ++ [(groups (normalize t)).flatMap Group.labels],c⟩ := by
                simpa [step,hc] using ho
              simp [he]
  | one g => exact attempt_budget n f h _ _ _ g o (by simpa [step,hc,prefixRoot] using ho)
  | two a b =>
    have hm : o ∈ (attempt f (normalize t) d c a).outputs ∨
        o ∈ (attempt f (normalize t) d c b).outputs := by simpa [step,hc,prefixRoot,combine] using ho
    rcases hm with hm | hm
    · exact attempt_budget n f h _ _ _ a o hm
    · exact attempt_budget n f h _ _ _ b o hm
  | refuse why => simp [step,hc] at ho

theorem run_zero_budget (t d c o) (ho : o ∈ (run 0 t d c).outputs) : o.sourceCuts = c := by
  have hat : ∀ t d c g, (attempt (fun _ _ _ => (⟨[],[],0,0,1⟩ : Receipt)) t d c g).outputs = [] := by
    intro t d c g
    unfold attempt
    split <;> first | rfl | (split <;> first | rfl | (split <;> rfl))
  cases hc : choose (normalize t) with
  | finish => have he : o = ⟨d.map Group.labels ++ [(groups (normalize t)).flatMap Group.labels],c⟩ := by
                simpa [run,step,hc] using ho
              simp [he]
  | one g => simp [run,step,hc,prefixRoot,hat] at ho
  | two a b => simp [run,step,hc,prefixRoot,combine,hat] at ho
  | refuse why => simp [run,step,hc] at ho

theorem run_output_budget (q : Nat) (t d c o) (ho : o ∈ (run q t d c).outputs) :
    o.sourceCuts.length ≤ c.length + q := by
  induction q generalizing t d c o with
  | zero => simp [run_zero_budget t d c o ho]
  | succ q ih => exact step_budget q (run q) (by intros; apply ih; assumption) t d c o ho

theorem generate_output_budget (t : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate t color q).outputs) : o.sourceCuts.length ≤ q := by
  unfold generate at ho
  split at ho
  · have hb := run_output_budget _ _ _ _ o ho
    simp only [List.length_nil,Nat.zero_add] at hb
    exact Nat.le_trans hb (Nat.min_le_left _ _)
  · simp at ho

/-- Concrete original-label refinement with a paid output inside the requested
ordinary cut budget. No original-edge component realization is inferred. -/
theorem generate_partition_coverage_paid (t : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hnd : (leaves t).Nodup)
    (hp : partitionCheck (leaves t) bs = true) (he : pairwiseEmbeddings t bs = true)
    (hm : ∀ b, b ∈ bs → LabelMonochromatic color b)
    (q : Nat) (hq : bs.length - 1 ≤ q) :
    ∃ o, o ∈ (generate t color q).outputs ∧ RefinesBlocks bs o.partition ∧ o.sourceCuts.length ≤ q := by
  obtain ⟨o,ho,hr⟩ := generate_partition_coverage t bs color hnd hp he hm q hq
  exact ⟨o,ho,hr,generate_output_budget t color q o ho⟩

end Universal233.SourceCoverage
