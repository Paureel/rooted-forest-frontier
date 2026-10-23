import ForestReverse
namespace GenericForest
open RMAF RestrictionBridge ForestState OutputState ForestGroups VertexGeometry
open Universal233 Universal233.CoreProgram Universal233.PaidQueries

def accepted (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest) : Bool :=
  agrees T ss F && decide (additionalCost ss F ≤ q)

def checked (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest) : Option Forest :=
  if accepted T ss q F then some F else none

def disjointSolve (t : Tree) (ss : List Tree)
    (ordinary : Tree → Tree → Nat → Option Forest) (q : Nat) : Option Forest :=
  (disjointAttempt t ss ordinary q).bind fun r =>
    r.answers.bind fun xs => checked (some t) ss q (xs.flatMap Prod.snd)

def branches (t : Tree) (ss : List Tree) (h : Overlap) (q : Nat) : List (Nat × Output) :=
  ((raw t ss h.left h.vertex q).map (h.left,·)) ++
    ((raw t ss h.right h.vertex q).map (h.right,·))

/-- Actual generic source-forest program. The sole recursive external callback
is the printed ordinary-tree IH. Overlap recursion uses every literal occurrence
of the two raw lists; no deduplication or source cut subset filtering occurs. -/
def solve (ordinary : Tree → Tree → Nat → Option Forest)
    (T : Option Tree) (ss : List Tree) (q : Nat) : Option Forest :=
  if proper T ss then
    if agrees T ss (ss.map leaves) then some (ss.map leaves) else
    match T, ss with
    | none, _ => none
    | some t, [s] => (ordinary t s q).bind (checked (some t) [s] q)
    | some t, _ =>
      match overlap t ss with
      | none => disjointSolve t ss ordinary q
      | some h =>
        let answers := (branches t ss h q).filterMap fun io =>
          let d := io.2.sourceCuts.length
          if _hd : 1 ≤ d ∧ d ≤ q then solve ordinary T (replace ss io.1 io.2.partition) (q-d)
          else none
        best List.length (accepted T ss q) answers
  else none
termination_by q
decreasing_by omega

theorem recursion_budget_decreases (q d : Nat) (h : 1 ≤ d ∧ d ≤ q) : q-d < q := by omega

theorem checked_sound (T : Option Tree) (ss : List Tree) (q : Nat) (F G : Forest)
    (h : checked T ss q F = some G) :
    G = F ∧ agrees T ss G = true ∧ additionalCost ss G ≤ q := by
  unfold checked at h
  split at h
  · have he : F = G := Option.some.inj h
    subst G
    rename_i ha
    exact ⟨rfl,by simpa [accepted] using ha⟩
  · simp at h

/-- Soundness is unconditional because every final return executes the original
literal ForestState checks. This does not establish completeness or minimum. -/
theorem solve_sound (ordinary : Tree → Tree → Nat → Option Forest)
    (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest)
    (h : solve ordinary T ss q = some F) :
    agrees T ss F = true ∧ additionalCost ss F ≤ q := by
  rw [solve.eq_def] at h
  split at h
  · split at h
    · have he : ss.map leaves = F := Option.some.inj h
      subst F
      rename_i hh
      exact ⟨hh,by simp [additionalCost]⟩
    · split at h
      · simp at h
      · rename_i t s
        obtain ⟨G,hG,hc⟩ := Option.bind_eq_some_iff.1 h
        have hh := checked_sound _ _ _ _ _ hc
        exact hh.2
      · rename_i t a b rest
        split at h
        · unfold disjointSolve at h
          obtain ⟨r,hr,hx⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨xs,hxs,hc⟩ := Option.bind_eq_some_iff.1 hx
          exact (checked_sound _ _ _ _ _ hc).2
        · exact (best_spec List.length (accepted (some t) ss q) _ F h).2.1 |> fun hh => by
            simpa [accepted] using hh
  · simp at h

structure OrdinaryIH (ordinary : Tree → Tree → Nat → Option Forest) where
  sound : ∀ t s q F, DepthOne.proper t s = true → ordinary t s q = some F →
    agreement t s F = true ∧ F.length-1 ≤ q ∧
      ∀ G, agreement t s G = true → F.length ≤ G.length
  complete : ∀ t s q G, DepthOne.proper t s = true → agreement t s G = true →
    G.length-1 ≤ q → ∃ F, ordinary t s q = some F

def ExactAt (f : Option Tree → List Tree → Nat → Option Forest) : Prop :=
  (∀ T ss q F, f T ss q = some F → agrees T ss F = true ∧ additionalCost ss F ≤ q) ∧
  (∀ T ss q G, agrees T ss G = true → additionalCost ss G ≤ q →
    ∃ F, f T ss q = some F ∧ F.length ≤ G.length)

-- First remaining mathematical assembly obligation: concrete paid scheduler,
-- actual restricted pairs, and literal ForestState reconstruction.
def DisjointExact (ordinary : Tree → Tree → Nat → Option Forest) : Prop :=
  ∀ t ss q G, agrees (some t) ss G = true →
    pairwiseEmbeddings t (ss.map leaves) = true → additionalCost ss G ≤ q →
    ∃ F, disjointSolve t ss ordinary q = some F ∧ F.length ≤ G.length

end GenericForest
