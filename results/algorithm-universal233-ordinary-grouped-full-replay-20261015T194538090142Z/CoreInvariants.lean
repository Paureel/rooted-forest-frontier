import CoreProgram

/-! Syntactic invariants of the executable candidate. These do not substitute
for connected-component realization of the recorded original cuts. -/
namespace Universal233.CoreProgram
open RMAF

def payload : GTree → List Nat
  | .leaf g => g.labels
  | .node _ l r => payload l ++ payload r

theorem normalize_payload (t : GTree) : payload (normalize t) = payload t := by
  induction t with
  | leaf g => rfl
  | node p l r ihl ihr =>
      cases hl : normalize l with
      | leaf a =>
          cases hr : normalize r with
          | leaf b =>
              simp only [normalize, hl, hr]
              split <;> simp_all [payload]
          | node q a b => simp_all [normalize, payload]
      | node q a b =>
          cases hr : normalize r <;> simp_all [normalize, payload]

def PureGroups (color : Nat → Nat) : GTree → Prop
  | .leaf g => ∀ x ∈ g.labels, color x = g.color
  | .node _ l r => PureGroups color l ∧ PureGroups color r

theorem fromTree_pure (color : Nat → Nat) (p : Vertex) (t : Tree) :
    PureGroups color (fromTree color p t) := by
  induction t generalizing p with
  | leaf x => simp [fromTree, PureGroups]
  | node l r ihl ihr => exact ⟨ihl _, ihr _⟩

theorem normalize_pure (color : Nat → Nat) (t : GTree) (h : PureGroups color t) :
    PureGroups color (normalize t) := by
  induction t with
  | leaf g => exact h
  | node p l r ihl ihr =>
      have hlp := ihl h.1
      have hrp := ihr h.2
      cases hl : normalize l with
      | leaf a =>
          rw [hl] at hlp
          cases hr : normalize r with
          | leaf b =>
              rw [hr] at hrp
              simp only [normalize, hl, hr]
              split
              · rename_i he
                intro x hx
                rcases List.mem_append.mp hx with hx | hx
                · exact hlp x hx
                · exact (hrp x hx).trans he.symm
              · exact ⟨hlp, hrp⟩
          | node q a b => simpa [normalize, hl, hr, PureGroups] using And.intro hlp hrp
      | node q a b =>
          cases hr : normalize r <;> simpa [normalize, hl, hr, PureGroups] using And.intro hlp hrp

def GoodCuts (cuts : List Vertex) : Prop :=
  cuts.Nodup ∧ ∀ v ∈ cuts, v ≠ []

theorem goodCuts_nil : GoodCuts [] := by simp [GoodCuts]

theorem goodCuts_cons {cuts : List Vertex} {v : Vertex}
    (h : GoodCuts cuts) (hr : v ≠ []) (hn : ¬cuts.contains v = true) : GoodCuts (v :: cuts) := by
  have hmem : v ∉ cuts := by
    intro hm
    exact hn (List.contains_iff_mem.mpr hm)
  refine ⟨List.nodup_cons.mpr ⟨hmem, h.1⟩, ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with he | hw
  · simpa [he] using hr
  · exact h.2 w hw

theorem attempt_outputs_good (f : GTree → List Group → List Vertex → Receipt)
    (h : ∀ t d c, GoodCuts c → ∀ o ∈ (f t d c).outputs, GoodCuts o.sourceCuts)
    (t d c g) (hc : GoodCuts c) (o) (ho : o ∈ (attempt f t d c g).outputs) :
    GoodCuts o.sourceCuts := by
  unfold attempt at ho
  split at ho
  · simp at ho
  · rename_i hroot
    split at ho
    · simp at ho
    · rename_i hdup
      split at ho
      · simp at ho
      · rename_i next he
        exact h next (g :: d) (g.origin :: c) (goodCuts_cons hc hroot hdup) o ho

theorem step_outputs_good (f : GTree → List Group → List Vertex → Receipt)
    (h : ∀ t d c, GoodCuts c → ∀ o ∈ (f t d c).outputs, GoodCuts o.sourceCuts)
    (t d c) (hc : GoodCuts c) (o) (ho : o ∈ (step f t d c).outputs) : GoodCuts o.sourceCuts := by
  cases hs : choose (normalize t) with
  | finish =>
      have he : o = ⟨d.map Group.labels ++ [(groups (normalize t)).flatMap Group.labels], c⟩ := by
        simpa [step, hs] using ho
      simpa [he] using hc
  | one g => exact attempt_outputs_good f h _ d c g hc o (by simpa [step, hs, prefixRoot] using ho)
  | two a b =>
      have he : o ∈ (attempt f (normalize t) d c a).outputs ∨
          o ∈ (attempt f (normalize t) d c b).outputs := by
        simpa [step, hs, prefixRoot, combine] using ho
      rcases he with he | he
      · exact attempt_outputs_good f h _ d c a hc o he
      · exact attempt_outputs_good f h _ d c b hc o he
  | refuse why => simp [step, hs] at ho

theorem run_outputs_good (q : Nat) (t d c) (hc : GoodCuts c) (o)
    (ho : o ∈ (run q t d c).outputs) : GoodCuts o.sourceCuts := by
  induction q generalizing t d c o with
  | zero =>
      exact step_outputs_good _ (by intros; contradiction) t d c hc o ho
  | succ q ih => exact step_outputs_good (run q) (by intros; exact ih _ _ _ ‹_› _ ‹_›) t d c hc o ho

/-- Every emitted cut record is nonroot and no original address is repeated.
This says nothing yet about graph nonredundancy or leafless components. -/
theorem generate_cut_records (t : Tree) (color : Nat → Nat) (q : Nat) (o)
    (ho : o ∈ (generate t color q).outputs) : GoodCuts o.sourceCuts := by
  unfold generate at ho
  split at ho
  · exact run_outputs_good _ _ _ _ goodCuts_nil o ho
  · simp at ho

def OutputShape (o : Output) : Prop := o.partition.length = o.sourceCuts.length + 1

theorem attempt_output_shape (f : GTree → List Group → List Vertex → Receipt)
    (h : ∀ t d c, d.length = c.length → ∀ o ∈ (f t d c).outputs, OutputShape o)
    (t d c g) (hc : d.length = c.length) (o) (ho : o ∈ (attempt f t d c g).outputs) :
    OutputShape o := by
  unfold attempt at ho
  split at ho
  · simp at ho
  · split at ho
    · simp at ho
    · split at ho
      · simp at ho
      · exact h _ _ _ (by simpa using hc) o ho

theorem step_output_shape (f : GTree → List Group → List Vertex → Receipt)
    (h : ∀ t d c, d.length = c.length → ∀ o ∈ (f t d c).outputs, OutputShape o)
    (t d c) (hc : d.length = c.length) (o) (ho : o ∈ (step f t d c).outputs) : OutputShape o := by
  cases hs : choose (normalize t) with
  | finish =>
      have he : o = ⟨d.map Group.labels ++ [(groups (normalize t)).flatMap Group.labels], c⟩ := by
        simpa [step, hs] using ho
      simp [he, OutputShape, hc]
  | one g => exact attempt_output_shape f h _ d c g hc o (by simpa [step, hs, prefixRoot] using ho)
  | two a b =>
      have he : o ∈ (attempt f (normalize t) d c a).outputs ∨
          o ∈ (attempt f (normalize t) d c b).outputs := by
        simpa [step, hs, prefixRoot, combine] using ho
      rcases he with he | he
      · exact attempt_output_shape f h _ d c a hc o he
      · exact attempt_output_shape f h _ d c b hc o he
  | refuse why => simp [step, hs] at ho

theorem run_output_shape (q : Nat) (t d c) (hc : d.length = c.length) (o)
    (ho : o ∈ (run q t d c).outputs) : OutputShape o := by
  induction q generalizing t d c o with
  | zero => exact step_output_shape _ (by intros; contradiction) t d c hc o ho
  | succ q ih => exact step_output_shape (run q) (by intros; exact ih _ _ _ ‹_› _ ‹_›) t d c hc o ho

/-- Equality of the recorded charge and pieces minus one. Actual source-cut
realization with this charge remains an explicitly separate graph obligation. -/
theorem generate_recorded_charge (t : Tree) (color : Nat → Nat) (q : Nat) (o)
    (ho : o ∈ (generate t color q).outputs) : o.partition.length = o.sourceCuts.length + 1 := by
  unfold generate at ho
  split at ho
  · exact run_output_shape _ _ _ _ rfl o ho
  · simp at ho

#print axioms normalize_payload
#print axioms fromTree_pure
#print axioms normalize_pure
#print axioms goodCuts_cons
#print axioms attempt_outputs_good
#print axioms step_outputs_good
#print axioms run_outputs_good
#print axioms generate_cut_records
#print axioms attempt_output_shape
#print axioms step_output_shape
#print axioms run_output_shape
#print axioms generate_recorded_charge
end Universal233.CoreProgram
