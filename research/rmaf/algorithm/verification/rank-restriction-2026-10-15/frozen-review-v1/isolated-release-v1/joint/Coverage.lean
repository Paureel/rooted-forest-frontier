import FullTransport

/-! One-shot finite owner budget and payload refinement for actual run/step.
The finite cover is derived from input Boolean checks in the entrypoint module;
no field of SourcePartition is a generator-coverage assertion. -/
namespace Universal233.SourceCoverage
open RMAF CoreGraph CoreProgram Integration

/-- The list may contain duplicates. Its length is an honest upper bound. -/
def OwnerCover (t : GTree) (P : SourcePartition (skeleton t)) (ids : List Nat) : Prop :=
  ∀ v g, GroupLeafAt t v g → P.owner v ∈ ids

def SourceRefines (t : GTree) (P : SourcePartition (skeleton t))
    (blocks : List (List Nat)) : Prop :=
  ∀ v g, GroupLeafAt t v g → ∃ b, b ∈ blocks ∧
    ∀ w a, GroupLeafAt t w a → P.owner w = P.owner v → ∀ x, x ∈ a.labels → x ∈ b

def DetachedKept (d : List Group) (blocks : List (List Nat)) : Prop :=
  ∀ g, g ∈ d → g.labels ∈ blocks

theorem ownerCover_nonempty (t : GTree) (P : SourcePartition (skeleton t))
    (ids : List Nat) (h : OwnerCover t P ids) : 0 < ids.length := by
  cases hgs : groups t with
  | nil => exact False.elim (groups_nonempty t hgs)
  | cons g rest =>
    obtain ⟨v,hv⟩ := groupLeaf_of_groups_mem t g (by simp [hgs])
    have hi := h v g hv
    exact List.length_pos_of_mem hi

noncomputable def ownerImage (t u : GTree) (P : SourcePartition (skeleton t))
    (Q : SourcePartition (skeleton u)) (f : RMAF.Vertex → RMAF.Vertex) (i : Nat) : Nat := by
  classical
  exact if h : ∃ v g, GroupLeafAt t v g ∧ P.owner v = i then Q.owner (f h.choose) else 0

theorem ownerImage_at (t u : GTree) (P : SourcePartition (skeleton t))
    (Q : SourcePartition (skeleton u)) (f : RMAF.Vertex → RMAF.Vertex)
    (hr : ∀ v w g a, GroupLeafAt t v g → GroupLeafAt t w a →
      P.owner v = P.owner w → Q.owner (f v) = Q.owner (f w))
    (v : RMAF.Vertex) (g : Group) (hv : GroupLeafAt t v g) :
    ownerImage t u P Q f (P.owner v) = Q.owner (f v) := by
  classical
  have he : ∃ w a, GroupLeafAt t w a ∧ P.owner w = P.owner v := ⟨v,g,hv,rfl⟩
  rw [ownerImage,dite_eq_left he]
  obtain ⟨a,ha,hoa⟩ := he.choose_spec
  exact hr _ v a g ha hv hoa

theorem fullTransport_ownerCover {t u : GTree}
    {P : SourcePartition (skeleton t)} {Q : SourcePartition (skeleton u)}
    (h : FullTransport t u P Q) (ids : List Nat) (hc : OwnerCover t P ids) :
    ∃ js : List Nat, js.length = ids.length ∧ OwnerCover u Q js := by
  obtain ⟨f,hf,hr,hs⟩ := h
  refine ⟨ids.map (ownerImage t u P Q f),by simp,?_⟩
  intro w a ha
  obtain ⟨v,g,hv,he⟩ := hs w a ha
  have hm := List.mem_map.mpr ⟨P.owner v,hc v g hv,ownerImage_at t u P Q f hr v g hv⟩
  simpa only [he] using hm

theorem fullTransport_refines {t u : GTree}
    {P : SourcePartition (skeleton t)} {Q : SourcePartition (skeleton u)}
    (h : FullTransport t u P Q) (blocks : List (List Nat))
    (hr : SourceRefines u Q blocks) : SourceRefines t P blocks := by
  obtain ⟨f,hf,he,hs⟩ := h
  intro v g hv
  obtain ⟨a,ha,hga⟩ := hf v g hv
  obtain ⟨b,hb,hcover⟩ := hr (f v) a ha
  refine ⟨b,hb,?_⟩
  intro w c hw how x hx
  obtain ⟨d,hd,hcd⟩ := hf w c hw
  exact hcover (f w) d hd (he w v c g hw hv how) x (hcd x hx)

theorem filter_owner_decreases (ids : List Nat) (i : Nat) (hi : i ∈ ids) :
    (ids.filter (fun j => j != i)).length < ids.length := by
  have hle := List.length_filter_le (fun j => j != i) ids
  have hne : (ids.filter (fun j => j != i)).length ≠ ids.length := by
    intro he
    have hh := List.length_filter_eq_length_iff.mp he i hi
    simp at hh
  omega

theorem erase_ownerCover (t u : GTree) (P : SourcePartition (skeleton t))
    (Q : SourcePartition (skeleton u)) (v : RMAF.Vertex)
    (e : RMAF.Vertex → RMAF.Vertex)
    (hlift : ∀ a b, GroupLeafAt u a b → GroupLeafAt t (e a) b ∧ Q.owner a = P.owner (e a))
    (habs : ∀ a b, GroupLeafAt u a b → Q.owner a ≠ P.owner v)
    (ids : List Nat) (hc : OwnerCover t P ids) :
    OwnerCover u Q (ids.filter (fun i => i != P.owner v)) := by
  intro a b hb
  obtain ⟨ht,ho⟩ := hlift a b hb
  have hm : Q.owner a ∈ ids := ho ▸ hc (e a) b ht
  simpa only [List.mem_filter,bne_iff_ne] using And.intro hm (habs a b hb)

theorem erase_refines (t u : GTree) (P : SourcePartition (skeleton t))
    (Q : SourcePartition (skeleton u)) (v : RMAF.Vertex) (g : Group)
    (hv : GroupLeafAt t v g) (hs : SingletonBlock P v)
    (e : RMAF.Vertex → RMAF.Vertex)
    (hlift : ∀ a b, GroupLeafAt u a b → GroupLeafAt t (e a) b ∧ Q.owner a = P.owner (e a))
    (hsurv : ∀ a b, GroupLeafAt t a b → a ≠ v → ∃ w, GroupLeafAt u w b ∧ e w = a)
    (blocks : List (List Nat)) (hkept : g.labels ∈ blocks)
    (hr : SourceRefines u Q blocks) : SourceRefines t P blocks := by
  intro a b hb
  by_cases hoa : P.owner a = P.owner v
  · refine ⟨g.labels,hkept,?_⟩
    intro w c hw how x hx
    have hwv := hs w c.color (groupLeaf_skeleton t w c hw) (how.trans hoa)
    subst w
    have hcg : c = g := Option.some.inj (hw.symm.trans hv)
    simpa only [hcg] using hx
  · have han : a ≠ v := by intro he; exact hoa (congrArg P.owner he)
    obtain ⟨a',ha',hea⟩ := hsurv a b hb han
    obtain ⟨out,hout,hcovers⟩ := hr a' b ha'
    refine ⟨out,hout,?_⟩
    intro w c hw how x hx
    have hwn : w ≠ v := by intro he; exact hoa (how.symm.trans (congrArg P.owner he))
    obtain ⟨w',hw',hew⟩ := hsurv w c hw hwn
    have hoa' := (hlift a' b ha').2
    have how' := (hlift w' c hw').2
    rw [hea] at hoa'
    rw [hew] at how'
    exact hcovers w' c hw' (how'.trans (how.trans hoa'.symm)) x hx

/-- One actual step consumes a source-owner budget. The continuation hypothesis
is ordinary induction on smaller finite lists, not a supplied coverage field. -/
theorem step_coverage (cap : Nat) (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (hcont : ∀ u d c (P : SourcePartition (skeleton u)) ids,
      (origins u).Nodup → RootZeroOnly u → CutsAvoid u c → Monochromatic P id →
      OwnerCover u P ids → ids.length ≤ cap →
      ∃ o, o ∈ (f u d c).outputs ∧ SourceRefines u P o.partition ∧ DetachedKept d o.partition)
    (t : GTree) (d : List Group) (c : List RMAF.Vertex)
    (hn : (origins t).Nodup) (hz : RootZeroOnly t) (ha : CutsAvoid t c)
    (P : SourcePartition (skeleton t)) (hm : Monochromatic P id)
    (ids : List Nat) (hcov : OwnerCover t P ids) (hlen : ids.length ≤ cap + 1) :
    ∃ o, o ∈ (step f t d c).outputs ∧ SourceRefines t P o.partition ∧ DetachedKept d o.partition := by
  obtain ⟨Q,hQ,hPQ⟩ := normalize_full_transport t P hm
  obtain ⟨js,hjs,hcovQ⟩ := fullTransport_ownerCover hPQ ids hcov
  have hjlen : js.length ≤ cap + 1 := by omega
  have hnn := normalize_origins_nodup t hn
  have hzn := normalize_rootZeroOnly t hz
  have han := normalize_cutsAvoid t c ha
  have hbranch : ∀ v g, GroupLeafAt (normalize t) v g → v ≠ [] → SingletonBlock Q v →
      ∃ o, o ∈ (attempt f (normalize t) d c g).outputs ∧
        SourceRefines (normalize t) Q o.partition ∧ DetachedKept d o.partition := by
    intro v g hv hvr hs
    obtain ⟨u,hu,hat,hn',hz',ha',R,hR,e,hlift,hsurv,habs⟩ :=
      attempt_singleton_source f (normalize t) d c hnn hzn han Q hQ v g hv hvr hs
    let ks := js.filter (fun i => i != Q.owner v)
    have hkcover : OwnerCover u R ks := erase_ownerCover (normalize t) u Q R v e hlift habs js hcovQ
    have hklen : ks.length ≤ cap := by
      have hdec := filter_owner_decreases js (Q.owner v) (hcovQ v g hv)
      change (js.filter (fun i => i != Q.owner v)).length ≤ cap
      omega
    obtain ⟨o,ho,hr,hkeep⟩ := hcont u (g :: d) (g.origin :: c) R ks hn' hz' ha' hR hkcover hklen
    refine ⟨o,by simpa only [hat] using ho,?_,?_⟩
    · exact erase_refines (normalize t) u Q R v g hv hs e hlift hsurv o.partition
        (hkeep g (by simp)) hr
    · intro a hab
      exact hkeep a (List.mem_cons_of_mem g hab)
  have hlocal : ∃ o, o ∈ (step f t d c).outputs ∧
      SourceRefines (normalize t) Q o.partition ∧ DetachedKept d o.partition := by
    cases hc : choose (normalize t) with
    | finish =>
      let o : Output := ⟨d.map Group.labels ++ [(groups (normalize t)).flatMap Group.labels],c⟩
      refine ⟨o,by simp [step,hc,o],?_,?_⟩
      · intro v g hv
        refine ⟨(groups (normalize t)).flatMap Group.labels,by simp [o],?_⟩
        intro w a hw how x hx
        exact List.mem_flatMap.mpr ⟨a,groupLeaf_mem_groups _ w a hw,hx⟩
      · intro g hg
        exact List.mem_append_left _ (List.mem_map.mpr ⟨g,hg,rfl⟩)
    | one g =>
      obtain ⟨v,hv,hvr,hs⟩ := choose_one_source_singleton (normalize t) hnn Q hQ g hc
      obtain ⟨o,ho,hr,hk⟩ := hbranch v g hv hvr hs
      exact ⟨o,by simpa only [step,hc,prefixRoot] using ho,hr,hk⟩
    | two a b =>
      obtain ⟨v,g,hg,hv,hvr,hs⟩ := choose_two_source_singleton (normalize t) Q hQ a b hc
      obtain ⟨o,ho,hr,hk⟩ := hbranch v g hv hvr hs
      refine ⟨o,?_,hr,hk⟩
      simp only [step,hc,prefixRoot,combine,List.mem_append]
      rcases hg with hg | hg
      · exact Or.inl (hg ▸ ho)
      · exact Or.inr (hg ▸ ho)
    | refuse why => exact False.elim (choose_normalized_no_refusal (normalize t) (normalize_fullyNormalized t) why hc)
  obtain ⟨o,ho,hr,hk⟩ := hlocal
  exact ⟨o,ho,fullTransport_refines hPQ o.partition hr,hk⟩

/-- Actual finite-budget coverage and original group payload refinement. The
q=0 continuation has no outputs, so the proof must rule it out using the finite
owner measure; pruning is never treated as a successful emission. -/
theorem run_coverage (q : Nat) (t : GTree) (d : List Group) (c : List RMAF.Vertex)
    (hn : (origins t).Nodup) (hz : RootZeroOnly t) (ha : CutsAvoid t c)
    (P : SourcePartition (skeleton t)) (hm : Monochromatic P id)
    (ids : List Nat) (hcov : OwnerCover t P ids) (hlen : ids.length ≤ q + 1) :
    ∃ o, o ∈ (run q t d c).outputs ∧ SourceRefines t P o.partition ∧ DetachedKept d o.partition := by
  induction q generalizing t d c P ids with
  | zero =>
    apply step_coverage 0 (fun _ _ _ => ⟨[],[],0,0,1⟩) _ t d c hn hz ha P hm ids hcov hlen
    intro u ds cs R js hnu hzu hau hR hcover hlength
    have hpos := ownerCover_nonempty u R js hcover
    omega
  | succ q ih =>
    apply step_coverage (q + 1) (run q) _ t d c hn hz ha P hm ids hcov hlen
    intro u ds cs R js hnu hzu hau hR hcover hlength
    exact ih u ds cs hnu hzu hau R hR js hcover hlength

end Universal233.SourceCoverage
