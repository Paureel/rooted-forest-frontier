import Branches

/-! One-shot reachable record invariants for actual attempt guards. These prove
successful exact source erasures, not original cut-component realization. -/
namespace Universal233.Integration
open RMAF CoreGraph CoreProgram List

def nonrootOrigins : GTree → List RMAF.Vertex
  | .leaf _ => []
  | .node _ l r => origins l ++ origins r

def RootZeroOnly (t : GTree) : Prop := [] ∉ nonrootOrigins t

def CutsAvoid (t : GTree) (cuts : List RMAF.Vertex) : Prop :=
  ∀ v, v ∈ cuts → v ∉ origins t

theorem nonrootOrigins_sublist (t : GTree) : nonrootOrigins t <+ origins t := by
  cases t with
  | leaf g => exact nil_sublist _
  | node p l r => exact sublist_cons_self _ _

theorem fromTree_rootZeroOnly (color : Nat → Nat) (T : Tree) : RootZeroOnly (fromTree color [] T) := by
  cases T with
  | leaf x => simp [RootZeroOnly,nonrootOrigins,fromTree]
  | node l r =>
    intro hh
    simp only [nonrootOrigins,fromTree,List.mem_append] at hh
    rcases hh with hh | hh
    · obtain ⟨q,hq⟩ := fromTree_origin_suffix color [false] l [] hh
      have hl := congrArg List.length hq
      simp at hl
    · obtain ⟨q,hq⟩ := fromTree_origin_suffix color [true] r [] hh
      have hl := congrArg List.length hq
      simp at hl

theorem normalize_nonroot_sublist (t : GTree) : nonrootOrigins (normalize t) <+ nonrootOrigins t := by
  cases t with
  | leaf g => exact .refl _
  | node p l r =>
    have hs := (normalize_origins_sublist l).append (normalize_origins_sublist r)
    cases hl : normalize l with
    | leaf a =>
      cases hr : normalize r with
      | leaf b =>
        simp only [normalize,hl,hr]
        split
        next => exact nil_sublist _
        next => simpa only [hl,hr,nonrootOrigins] using hs
      | node q a b => simp only [normalize,hl,hr]; simpa only [hl,hr,nonrootOrigins] using hs
    | node q a b => cases hr : normalize r <;> simp only [normalize,hl,hr] <;> simpa only [hl,hr,nonrootOrigins] using hs

theorem normalize_rootZeroOnly (t : GTree) (h : RootZeroOnly t) : RootZeroOnly (normalize t) := by
  intro hm
  exact h ((normalize_nonroot_sublist t).subset hm)

theorem erase_nonroot_sublist (t : GTree) (chosen : RMAF.Vertex) (u : GTree)
    (hu : erase chosen t = some u) : nonrootOrigins u <+ nonrootOrigins t := by
  cases t with
  | leaf g =>
    simp only [erase] at hu
    split at hu
    next => contradiction
    next => have he := Option.some.inj hu; subst u; exact .refl _
  | node p l r =>
    simp only [erase] at hu
    split at hu
    next => contradiction
    next =>
      cases el : erase chosen l with
      | none =>
        cases er : erase chosen r with
        | none => simp [el,er] at hu
        | some b =>
          simp only [el,er] at hu
          have he := Option.some.inj hu
          subst u
          exact ((nonrootOrigins_sublist b).trans (erase_origins_sublist r chosen b er)).trans (sublist_append_right _ _)
      | some a =>
        cases er : erase chosen r with
        | none =>
          simp only [el,er] at hu
          have he := Option.some.inj hu
          subst u
          exact ((nonrootOrigins_sublist a).trans (erase_origins_sublist l chosen a el)).trans (sublist_append_left _ _)
        | some b =>
          simp only [el,er] at hu
          have he := Option.some.inj hu
          subst u
          exact (erase_origins_sublist l chosen a el).append (erase_origins_sublist r chosen b er)

theorem erase_rootZeroOnly (t : GTree) (chosen : RMAF.Vertex) (u : GTree)
    (hu : erase chosen t = some u) (h : RootZeroOnly t) : RootZeroOnly u := by
  intro hm
  exact h ((erase_nonroot_sublist t chosen u hu).subset hm)

theorem groupLeaf_origin_nonempty (t : GTree) (h : RootZeroOnly t)
    (v : RMAF.Vertex) (g : Group) (hv : GroupLeafAt t v g) (hvr : v ≠ []) : g.origin ≠ [] := by
  cases t with
  | leaf a => obtain ⟨rfl,he⟩ := (groupLeaf_leaf a g v).1 hv; exact False.elim (hvr rfl)
  | node p l r =>
    intro he
    cases v with
    | nil => exact False.elim (hvr rfl)
    | cons s v =>
      apply h
      cases s with
      | false => exact List.mem_append_left _ (he ▸ groupLeaf_origin_mem l v g hv)
      | true => exact List.mem_append_right _ (he ▸ groupLeaf_origin_mem r v g hv)

theorem erase_chosen_absent (t : GTree) (chosen : RMAF.Vertex) (u : GTree)
    (hu : erase chosen t = some u) : chosen ∉ origins u := by
  induction t generalizing u with
  | leaf g =>
    simp only [erase] at hu
    split at hu
    next => contradiction
    next hh =>
      have he := Option.some.inj hu
      subst u
      simpa [origins,eq_comm] using hh
  | node p l r ihl ihr =>
    simp only [erase] at hu
    split at hu
    next => contradiction
    next hp =>
      cases el : erase chosen l with
      | none =>
        cases er : erase chosen r with
        | none => simp [el,er] at hu
        | some b =>
          simp only [el,er] at hu
          have he := Option.some.inj hu
          subst u
          exact ihr b er
      | some a =>
        cases er : erase chosen r with
        | none =>
          simp only [el,er] at hu
          have he := Option.some.inj hu
          subst u
          exact ihl a el
        | some b =>
          simp only [el,er] at hu
          have he := Option.some.inj hu
          subst u
          simp [origins,Ne.symm hp,ihl a el,ihr b er]

theorem normalize_cutsAvoid (t : GTree) (cuts : List RMAF.Vertex) (h : CutsAvoid t cuts) :
    CutsAvoid (normalize t) cuts := by
  intro v hv hm
  exact h v hv ((normalize_origins_sublist t).subset hm)

theorem erase_cutsAvoid (t : GTree) (cuts : List RMAF.Vertex) (chosen : RMAF.Vertex) (u : GTree)
    (hu : erase chosen t = some u) (h : CutsAvoid t cuts) : CutsAvoid u (chosen :: cuts) := by
  intro v hv
  simp only [List.mem_cons] at hv
  rcases hv with he | hv
  · subst v
    exact erase_chosen_absent t chosen u hu
  · intro hm
    exact h v hv ((erase_origins_sublist t chosen u hu).subset hm)

/-- An exact selected singleton detachment reaches the continuation of attempt;
its root, duplicate and whole-source refusal guards all provably fail. The
resulting actual source partition and original payload lift are constructed. -/
theorem attempt_singleton_source (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (t : GTree) (detached : List Group) (cuts : List RMAF.Vertex)
    (hn : (origins t).Nodup) (hz : RootZeroOnly t) (ha : CutsAvoid t cuts)
    (P : SourcePartition (skeleton t)) (hm : Monochromatic P id)
    (v : RMAF.Vertex) (g : Group) (hv : GroupLeafAt t v g) (hvr : v ≠ []) (hs : SingletonBlock P v) :
    ∃ u, erase g.origin t = some u ∧
      attempt f t detached cuts g =
        { f u (g :: detached) (g.origin :: cuts) with
          childAttempts := (f u (g :: detached) (g.origin :: cuts)).childAttempts + 1 } ∧
      (origins u).Nodup ∧ RootZeroOnly u ∧ CutsAvoid u (g.origin :: cuts) ∧
      ∃ Q : SourcePartition (skeleton u), Monochromatic Q id ∧
        ∃ e : RMAF.Vertex → RMAF.Vertex,
        (∀ a b, GroupLeafAt u a b → GroupLeafAt t (e a) b ∧ Q.owner a = P.owner (e a)) ∧
        (∀ a b, GroupLeafAt t a b → a ≠ v → ∃ w, GroupLeafAt u w b ∧ e w = a) ∧
        (∀ a b, GroupLeafAt u a b → Q.owner a ≠ P.owner v) := by
  have hgn := groupLeaf_origin_nonempty t hz v g hv hvr
  have hgc : g.origin ∉ cuts := by intro hc; exact ha g.origin hc (groupLeaf_origin_mem t v g hv)
  obtain ⟨u,hu,Q,hQ,e,hlift,hsurv,habs⟩ := erase_leaf_source_transport t hn v g hv hvr P hm hs
  refine ⟨u,hu,?_,erase_origins_nodup t _ u hu hn,erase_rootZeroOnly t _ u hu hz,
    erase_cutsAvoid t cuts _ u hu ha,Q,hQ,e,hlift,hsurv,habs⟩
  simp [attempt,hgn,hgc,hu]

/-- A proved continuation fact for the exact production attempt. No field in
this proposition is accepted as an input to the source progress theorem below. -/
def SourceAttempt (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (t : GTree) (detached : List Group) (cuts : List RMAF.Vertex)
    (P : SourcePartition (skeleton t)) (v : RMAF.Vertex) (g : Group) : Prop :=
  ∃ u, erase g.origin t = some u ∧
      attempt f t detached cuts g =
        { f u (g :: detached) (g.origin :: cuts) with
          childAttempts := (f u (g :: detached) (g.origin :: cuts)).childAttempts + 1 } ∧
      (origins u).Nodup ∧ RootZeroOnly u ∧ CutsAvoid u (g.origin :: cuts) ∧
      ∃ Q : SourcePartition (skeleton u), Monochromatic Q id ∧
        ∃ e : RMAF.Vertex → RMAF.Vertex,
        (∀ a b, GroupLeafAt u a b → GroupLeafAt t (e a) b ∧ Q.owner a = P.owner (e a)) ∧
        (∀ a b, GroupLeafAt t a b → a ≠ v → ∃ w, GroupLeafAt u w b ∧ e w = a) ∧
        (∀ a b, GroupLeafAt u a b → Q.owner a ≠ P.owner v)

/-- Actual source progress of the exact normalization, chooser, guards, erase
and continuation call. Each nonfinish case has a target-preserving branch;
its valid suppressed graph and original group lift are constructed above.
The statement does not certify the original edge's residual components or
that a finite cut budget reaches an output. -/
theorem step_source_progress (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (t : GTree) (detached : List Group) (cuts : List RMAF.Vertex)
    (hn : (origins t).Nodup) (hz : RootZeroOnly t) (ha : CutsAvoid t cuts)
    (P : SourcePartition (skeleton t)) (hm : Monochromatic P id) :
    ∃ Q : SourcePartition (skeleton (normalize t)), Monochromatic Q id ∧
      GroupedTransport t (normalize t) P Q ∧
      (choose (normalize t) = .finish ∨ ∃ v g,
        GroupLeafAt (normalize t) v g ∧ v ≠ [] ∧ SingletonBlock Q v ∧
        (choose (normalize t) = .one g ∨ ∃ a b,
          choose (normalize t) = .two a b ∧ (g = a ∨ g = b)) ∧
        SourceAttempt f (normalize t) detached cuts Q v g) := by
  obtain ⟨Q,hQ,hPQ⟩ := normalize_source_transport t P hm
  have hnn := normalize_origins_nodup t hn
  have hzn := normalize_rootZeroOnly t hz
  have han := normalize_cutsAvoid t cuts ha
  refine ⟨Q,hQ,hPQ,?_⟩
  cases hc : choose (normalize t) with
  | finish => exact Or.inl rfl
  | one g =>
    obtain ⟨v,hv,hvr,hs⟩ := choose_one_source_singleton (normalize t) hnn Q hQ g hc
    exact Or.inr ⟨v,g,hv,hvr,hs,Or.inl rfl,
      attempt_singleton_source f (normalize t) detached cuts hnn hzn han Q hQ v g hv hvr hs⟩
  | two a b =>
    obtain ⟨v,g,hg,hv,hvr,hs⟩ := choose_two_source_singleton (normalize t) Q hQ a b hc
    exact Or.inr ⟨v,g,hv,hvr,hs,Or.inr ⟨a,b,rfl,hg⟩,
      attempt_singleton_source f (normalize t) detached cuts hnn hzn han Q hQ v g hv hvr hs⟩
  | refuse why =>
    exact False.elim (choose_normalized_no_refusal (normalize t) (normalize_fullyNormalized t) why hc)

/-- The source progress theorem applies to the actual initial production state
created from the ordinary solver's exact source checks. -/
theorem initial_step_source_progress (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (t : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hp : RMAF.partitionCheck (RMAF.leaves t) bs = true)
    (he : RMAF.pairwiseEmbeddings t bs = true)
    (hm : ∀ b, b ∈ bs → VertexGeometry.LabelMonochromatic color b) :
    ∃ Q : SourcePartition (skeleton (normalize (fromTree color [] t))),
      Monochromatic Q id ∧
      GroupedTransport (fromTree color [] t) (normalize (fromTree color [] t))
        (initialPartition t bs color hp he) Q ∧
      (choose (normalize (fromTree color [] t)) = .finish ∨ ∃ v g,
        GroupLeafAt (normalize (fromTree color [] t)) v g ∧ v ≠ [] ∧ SingletonBlock Q v ∧
        (choose (normalize (fromTree color [] t)) = .one g ∨ ∃ a b,
          choose (normalize (fromTree color [] t)) = .two a b ∧ (g = a ∨ g = b)) ∧
        SourceAttempt f (normalize (fromTree color [] t)) [] [] Q v g) := by
  exact step_source_progress f (fromTree color [] t) [] []
    (fromTree_origins_nodup color [] t) (fromTree_rootZeroOnly color t)
    (by intro v hv; simp at hv) (initialPartition t bs color hp he)
    (initialPartition_monochromatic t bs color hp he hm)

end Universal233.Integration
