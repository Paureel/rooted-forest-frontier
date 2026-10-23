import CutRecords

/-! One-shot exact normalization transport with surjectivity on group occurrences.
This is a strengthening of the frozen forward transport, needed to account for
all live source owners, rather than silently forgetting newly displayed leaves. -/
namespace Universal233.SourceCoverage
open RMAF CoreGraph CoreProgram Integration

/-- A concrete old-to-new occurrence map; every new occurrence is its image. -/
def FullTransport (t u : GTree) (P : SourcePartition (skeleton t))
    (Q : SourcePartition (skeleton u)) : Prop :=
  ∃ f : RMAF.Vertex → RMAF.Vertex,
    (∀ v g, GroupLeafAt t v g → ∃ a, GroupLeafAt u (f v) a ∧
      ∀ x, x ∈ g.labels → x ∈ a.labels) ∧
    (∀ v w g a, GroupLeafAt t v g → GroupLeafAt t w a →
      P.owner v = P.owner w → Q.owner (f v) = Q.owner (f w)) ∧
    (∀ w a, GroupLeafAt u w a → ∃ v g, GroupLeafAt t v g ∧ f v = w)

theorem fullTransport_refl (t : GTree) (P : SourcePartition (skeleton t)) :
    FullTransport t t P P :=
  ⟨id,(by intro v g hv; exact ⟨g,hv,fun _ hx => hx⟩),
    (by intros; assumption),(by intro w a ha; exact ⟨w,a,ha,rfl⟩)⟩

theorem fullTransport_trans {t u v : GTree}
    {P : SourcePartition (skeleton t)} {Q : SourcePartition (skeleton u)}
    {R : SourcePartition (skeleton v)} (h : FullTransport t u P Q)
    (k : FullTransport u v Q R) : FullTransport t v P R := by
  obtain ⟨f,hf,hr,hfs⟩ := h
  obtain ⟨g,hg,hs,hgs⟩ := k
  refine ⟨g ∘ f,?_,?_,?_⟩
  · intro w a ha
    obtain ⟨b,hb,hlab⟩ := hf w a ha
    obtain ⟨c,hc,hlbc⟩ := hg (f w) b hb
    exact ⟨c,hc,fun x hx => hlbc x (hlab x hx)⟩
  · intro a b ga gb ha hb he
    obtain ⟨ga',ha',_⟩ := hf a ga ha
    obtain ⟨gb',hb',_⟩ := hf b gb hb
    exact hs _ _ _ _ ha' hb' (hr _ _ _ _ ha hb he)
  · intro w a ha
    obtain ⟨b,gb,hb,heb⟩ := hgs w a ha
    obtain ⟨c,gc,hc,hec⟩ := hfs b gb hb
    exact ⟨c,gc,hc,by simp [Function.comp_apply,hec,heb]⟩

theorem gcontract_projection_surjective {t u p c} (h : GContract t u p c)
    (w : RMAF.Vertex) (a : Group) (ha : GroupLeafAt u w a) :
    ∃ v g, GroupLeafAt t v g ∧ cherryProjection p v = w := by
  induction h generalizing w with
  | root origin x y hc =>
    obtain ⟨rfl,he⟩ := (groupLeaf_leaf _ a w).1 ha
    exact ⟨[false],x,rfl,rfl⟩
  | left origin r h ih =>
    cases w with
    | nil => simp [GroupLeafAt,groupAt] at ha
    | cons s w =>
      cases s with
      | false =>
        obtain ⟨v,g,hg,he⟩ := ih w ha
        exact ⟨false :: v,g,hg,by simpa [projection_cons] using congrArg (false :: ·) he⟩
      | true => exact ⟨true :: w,a,ha,by simp [cherryProjection]⟩
  | right origin l h ih =>
    cases w with
    | nil => simp [GroupLeafAt,groupAt] at ha
    | cons s w =>
      cases s with
      | false => exact ⟨false :: w,a,ha,by simp [cherryProjection]⟩
      | true =>
        obtain ⟨v,g,hg,he⟩ := ih w ha
        exact ⟨true :: v,g,hg,by simpa [projection_cons] using congrArg (true :: ·) he⟩

theorem gcontract_full_transport {t u p c} (h : GContract t u p c)
    (P : SourcePartition (skeleton t)) (hm : Monochromatic P id) :
    ∃ Q : SourcePartition (skeleton u), Monochromatic Q id ∧ FullTransport t u P Q := by
  have hc := gcontract_graph h
  have hch := contraction_cherry hc
  obtain ⟨P',hPP',hm',hs⟩ := homogeneous_cherry_coarsening P hch id hm rfl
  let Q := contractPartition hc P' hs
  refine ⟨Q,contractPartition_monochromatic hc P' hs id hm' rfl,?_⟩
  refine ⟨cherryProjection p,gcontract_group_image h,?_,gcontract_projection_surjective h⟩
  intro v w g a hv hw he
  have hlv := groupLeaf_skeleton t v g hv
  have hlw := groupLeaf_skeleton t w a hw
  have ho := hPP' _ _ _ _ hlv hlw he
  change (contractPartition hc P' hs).owner _ = (contractPartition hc P' hs).owner _
  rw [contractPartition_owner hc P' hs v g.color hlv,contractPartition_owner hc P' hs w a.color hlw]
  exact ho

theorem gcontracts_full_transport {t u} (h : GContracts t u)
    (P : SourcePartition (skeleton t)) (hm : Monochromatic P id) :
    ∃ Q : SourcePartition (skeleton u), Monochromatic Q id ∧ FullTransport t u P Q := by
  induction h with
  | refl => exact ⟨P,hm,fullTransport_refl _ _⟩
  | step hr hs ih =>
    obtain ⟨Q,hQ,hPQ⟩ := gcontract_full_transport hr P hm
    obtain ⟨R,hR,hQR⟩ := ih Q hQ
    exact ⟨R,hR,fullTransport_trans hPQ hQR⟩

theorem normalize_full_transport (t : GTree) (P : SourcePartition (skeleton t))
    (hm : Monochromatic P id) :
    ∃ Q : SourcePartition (skeleton (normalize t)), Monochromatic Q id ∧
      FullTransport t (normalize t) P Q :=
  gcontracts_full_transport (normalize_gcontracts t) P hm

end Universal233.SourceCoverage
