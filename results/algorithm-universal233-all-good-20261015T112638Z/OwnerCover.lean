import Realization

/-! A finite terminal-owner cover, transported without an owner-cardinality
oracle. Normalization maps the representative list; singleton erasure removes
at least one list element. This is a prospective coverage lemma, not a runtime
or mass result. -/
namespace Universal233.CutRealization
open RMAF CoreGraph CoreProgram Integration List

theorem gcontract_leaf_surjective {t u p c} (h : GContract t u p c)
    (w : RMAF.Vertex) (a : Group) (ha : GroupLeafAt u w a) :
    ∃ v g, GroupLeafAt t v g ∧ cherryProjection p v = w := by
  induction h generalizing w with
  | root origin x y hc =>
    obtain ⟨rfl,he⟩ := (groupLeaf_leaf _ a w).1 ha
    exact ⟨[false],x,rfl,by simp [cherryProjection]⟩
  | left origin r h ih =>
    cases w with
    | nil => simp [GroupLeafAt,groupAt] at ha
    | cons s w =>
      cases s with
      | false =>
        obtain ⟨v,g,hv,he⟩ := ih w ha
        exact ⟨false :: v,g,hv,by rw [projection_cons,he]⟩
      | true => exact ⟨true :: w,a,ha,by simp [cherryProjection]⟩
  | right origin l h ih =>
    cases w with
    | nil => simp [GroupLeafAt,groupAt] at ha
    | cons s w =>
      cases s with
      | false => exact ⟨false :: w,a,ha,by simp [cherryProjection]⟩
      | true =>
        obtain ⟨v,g,hv,he⟩ := ih w ha
        exact ⟨true :: v,g,hv,by rw [projection_cons,he]⟩

def FullTransport (t u : GTree) (P : SourcePartition (skeleton t))
    (Q : SourcePartition (skeleton u)) : Prop :=
  ∃ f : RMAF.Vertex → RMAF.Vertex,
    (∀ v g, GroupLeafAt t v g → ∃ a, GroupLeafAt u (f v) a ∧
      ∀ x, x ∈ g.labels → x ∈ a.labels) ∧
    (∀ v w g a, GroupLeafAt t v g → GroupLeafAt t w a →
      P.owner v = P.owner w → Q.owner (f v) = Q.owner (f w)) ∧
    (∀ w a, GroupLeafAt u w a → ∃ v g, GroupLeafAt t v g ∧ f v = w)

theorem FullTransport.grouped {t u P Q} (h : FullTransport t u P Q) : GroupedTransport t u P Q := by
  obtain ⟨f,hf,hc,hs⟩ := h
  exact ⟨f,hf,hc⟩

theorem fullTransport_refl (t : GTree) (P : SourcePartition (skeleton t)) : FullTransport t t P P :=
  ⟨id,(by intro v g hv; exact ⟨g,hv,fun _ hx => hx⟩),(by intros; assumption),
    (by intro w a ha; exact ⟨w,a,ha,rfl⟩)⟩

theorem fullTransport_trans {t u v P Q R} (h : FullTransport t u P Q) (k : FullTransport u v Q R) :
    FullTransport t v P R := by
  obtain ⟨f,hf,hc,hs⟩ := h
  obtain ⟨g,hg,kc,ks⟩ := k
  refine ⟨g ∘ f,?_,?_,?_⟩
  · intro w a ha
    obtain ⟨b,hb,hab⟩ := hf w a ha
    obtain ⟨c,hc,hbc⟩ := hg (f w) b hb
    exact ⟨c,hc,fun x hx => hbc x (hab x hx)⟩
  · intro a b ga gb ha hb he
    obtain ⟨ga',ha',_⟩ := hf a ga ha
    obtain ⟨gb',hb',_⟩ := hf b gb hb
    exact kc _ _ _ _ ha' hb' (hc _ _ _ _ ha hb he)
  · intro w a ha
    obtain ⟨x,b,hx,hxe⟩ := ks w a ha
    obtain ⟨y,c,hy,hye⟩ := hs x b hx
    exact ⟨y,c,hy,by simp [Function.comp_def,hye,hxe]⟩

theorem gcontract_full_transport {t u p c} (h : GContract t u p c)
    (P : SourcePartition (skeleton t)) (hm : Monochromatic P id) :
    ∃ Q : SourcePartition (skeleton u), Monochromatic Q id ∧ FullTransport t u P Q := by
  have hc := gcontract_graph h
  have hch := contraction_cherry hc
  obtain ⟨P',hPP',hm',hs⟩ := homogeneous_cherry_coarsening P hch id hm rfl
  let Q := contractPartition hc P' hs
  refine ⟨Q,contractPartition_monochromatic hc P' hs id hm' rfl,cherryProjection p,
    gcontract_group_image h,?_,gcontract_leaf_surjective h⟩
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
    ∃ Q : SourcePartition (skeleton (normalize t)), Monochromatic Q id ∧ FullTransport t (normalize t) P Q :=
  gcontracts_full_transport (normalize_gcontracts t) P hm

structure OwnerCover (t : GTree) (P : SourcePartition (skeleton t)) (reps : List RMAF.Vertex) : Prop where
  actual : ∀ r, r ∈ reps → ∃ g, GroupLeafAt t r g
  covers : ∀ v g, GroupLeafAt t v g → ∃ r, r ∈ reps ∧ P.owner r = P.owner v

theorem ownerCover_nonempty {t P reps} (h : OwnerCover t P reps) : reps ≠ [] := by
  have hg := groups_nonempty t
  cases he : groups t with
  | nil => exact False.elim (hg he)
  | cons g gs =>
    obtain ⟨v,hv⟩ := groupLeaf_of_groups_mem t g (by rw [he]; simp)
    obtain ⟨r,hr,_⟩ := h.covers v g hv
    intro hempty; simp [hempty] at hr

theorem fullTransport_cover {t u P Q reps} (h : FullTransport t u P Q) (hr : OwnerCover t P reps) :
    ∃ next, OwnerCover u Q next ∧ next.length = reps.length := by
  obtain ⟨f,hf,hc,hs⟩ := h
  refine ⟨reps.map f,?_,by simp⟩
  constructor
  · intro r hm
    obtain ⟨v,hv,rfl⟩ := List.mem_map.1 hm
    obtain ⟨g,hg⟩ := hr.actual v hv
    obtain ⟨a,ha,_⟩ := hf v g hg
    exact ⟨a,ha⟩
  · intro w a ha
    obtain ⟨v,g,hv,hvw⟩ := hs w a ha
    obtain ⟨r,hrm,hre⟩ := hr.covers v g hv
    obtain ⟨gr,hgr⟩ := hr.actual r hrm
    exact ⟨f r,List.mem_map.2 ⟨r,hrm,rfl⟩,by rw [←hvw]; exact hc r v gr g hgr hv hre⟩

theorem erase_owner_cover {t u P Q reps v g}
    (hr : OwnerCover t P reps) (hv : GroupLeafAt t v g) (hs : SingletonBlock P v)
    (e : RMAF.Vertex → RMAF.Vertex)
    (hlift : ∀ a b, GroupLeafAt u a b → GroupLeafAt t (e a) b ∧ Q.owner a = P.owner (e a))
    (hsurv : ∀ a b, GroupLeafAt t a b → a ≠ v → ∃ w, GroupLeafAt u w b ∧ e w = a)
    (habs : ∀ a b, GroupLeafAt u a b → Q.owner a ≠ P.owner v) :
    ∃ next, OwnerCover u Q next ∧ next.length < reps.length := by
  classical
  let survivor := reps.filter (fun a => a != v)
  let back := fun a : RMAF.Vertex =>
    if h : ∃ w, (∃ b, GroupLeafAt u w b) ∧ e w = a then h.choose else []
  have hb : ∀ a, a ∈ survivor → (∃ b, GroupLeafAt u (back a) b) ∧ e (back a) = a := by
    intro a ha
    obtain ⟨ham,han⟩ := List.mem_filter.1 ha
    have hne : a ≠ v := by simpa using han
    obtain ⟨b,hba⟩ := hr.actual a ham
    obtain ⟨w,hw,hwe⟩ := hsurv a b hba hne
    have hex : ∃ w, (∃ b, GroupLeafAt u w b) ∧ e w = a := ⟨w,⟨b,hw⟩,hwe⟩
    simpa only [back,dite_eq_left hex] using hex.choose_spec
  have hvrep : v ∈ reps := by
    obtain ⟨a,ha,hao⟩ := hr.covers v g hv
    obtain ⟨b,hba⟩ := hr.actual a ha
    have he : a = v := hs a b.color (groupLeaf_skeleton t a b hba) hao
    simpa only [he] using ha
  refine ⟨survivor.map back,?_,?_⟩
  · constructor
    · intro w hw
      obtain ⟨a,ha,rfl⟩ := List.mem_map.1 hw
      exact (hb a ha).1
    · intro w b hwb
      have hw := hlift w b hwb
      obtain ⟨a,ha,hao⟩ := hr.covers (e w) b hw.1
      have hane : a ≠ v := by
        intro he; subst a
        exact habs w b hwb (hw.2.trans hao.symm)
      have has : a ∈ survivor := List.mem_filter.2 ⟨ha,by simpa using hane⟩
      obtain ⟨bb,hbb⟩ := (hb a has).1
      have hbo := (hlift (back a) bb hbb).2
      refine ⟨back a,List.mem_map.2 ⟨a,has,rfl⟩,?_⟩
      rw [(hb a has).2] at hbo
      exact hbo.trans (hao.trans hw.2.symm)
  · simp only [List.length_map]
    exact List.length_filter_lt_length_iff_exists.2 ⟨v,hvrep,by simp⟩

end Universal233.CutRealization
