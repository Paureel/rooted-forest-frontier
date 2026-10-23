import OwnerCover

namespace Universal233.CutRealization
open RMAF CoreGraph CoreProgram Integration List

/-- Every original input block is already in one detached payload or all its
labels remain in current groups of one source owner. No refinement conclusion
is assumed. -/
def Tracked (bs : List (List Nat)) (t : GTree) (d : List Group)
    (P : SourcePartition (skeleton t)) : Prop :=
  ∀ b, b ∈ bs →
    (∃ g, g ∈ d ∧ ∀ x, x ∈ b → x ∈ g.labels) ∨
    (∃ i, ∀ x, x ∈ b → ∃ v g, GroupLeafAt t v g ∧ x ∈ g.labels ∧ P.owner v = i)

theorem tracked_normalize {bs t u d P Q} (h : Tracked bs t d P)
    (ht : GroupedTransport t u P Q) : Tracked bs u d Q := by
  obtain ⟨f,hf,hc⟩ := ht
  intro b hb
  rcases h b hb with hd | ⟨i,hi⟩
  · exact Or.inl hd
  · right
    cases b with
    | nil => exact ⟨0,by simp⟩
    | cons x xs =>
      obtain ⟨v,g,hv,hx,hvo⟩ := hi x (by simp)
      refine ⟨Q.owner (f v),?_⟩
      intro y hy
      obtain ⟨w,a,hw,hya,hwo⟩ := hi y hy
      obtain ⟨a',ha',hlabel⟩ := hf w a hw
      exact ⟨f w,a',ha',hlabel y hya,hc w v a g hw hv (hwo.trans hvo.symm)⟩

theorem tracked_erase {bs t u d P Q v g}
    (h : Tracked bs t d P) (hv : GroupLeafAt t v g) (hs : SingletonBlock P v)
    (e : RMAF.Vertex → RMAF.Vertex)
    (hlift : ∀ a b, GroupLeafAt u a b → GroupLeafAt t (e a) b ∧ Q.owner a = P.owner (e a))
    (hsurv : ∀ a b, GroupLeafAt t a b → a ≠ v → ∃ w, GroupLeafAt u w b ∧ e w = a) :
    Tracked bs u (g :: d) Q := by
  intro b hb
  rcases h b hb with ⟨a,ha,hlab⟩ | ⟨i,hi⟩
  · exact Or.inl ⟨a,List.mem_cons_of_mem g ha,hlab⟩
  · by_cases he : i = P.owner v
    · left
      refine ⟨g,by simp,?_⟩
      intro x hx
      obtain ⟨w,a,hw,hxa,hwo⟩ := hi x hx
      have ew : w = v := hs w a.color (groupLeaf_skeleton t w a hw) (hwo.trans he)
      subst w
      have eg : a = g := Option.some.inj (hw.symm.trans hv)
      simpa only [eg] using hxa
    · right
      refine ⟨i,?_⟩
      intro x hx
      obtain ⟨w,a,hw,hxa,hwo⟩ := hi x hx
      have ew : w ≠ v := by intro ew; subst w; exact he hwo.symm
      obtain ⟨z,hz,hze⟩ := hsurv w a hw ew
      have hzo := (hlift z a hz).2
      rw [hze] at hzo
      exact ⟨z,a,hz,hxa,hzo.trans hwo⟩

theorem tracked_finish {bs t d P} (h : Tracked bs t d P) :
    VertexGeometry.Refines bs (d.map Group.labels ++ [(groups t).flatMap Group.labels]) := by
  intro b hb
  rcases h b hb with ⟨g,hg,hlabel⟩ | ⟨i,hi⟩
  · exact ⟨g.labels,List.mem_append_left _ (List.mem_map.2 ⟨g,hg,rfl⟩),hlabel⟩
  · refine ⟨(groups t).flatMap Group.labels,by simp,?_⟩
    intro x hx
    obtain ⟨v,g,hv,hxg,hvo⟩ := hi x hx
    exact List.mem_flatMap.2 ⟨g,groupLeaf_mem_groups t v g hv,hxg⟩

theorem History.record_invariants {T color t d c} (h : History T color t d c) :
    RootZeroOnly t ∧ CutsAvoid t c := by
  induction h with
  | initial => exact ⟨fromTree_rootZeroOnly _ _,by intro v hv; cases hv⟩
  | normalized h ih => exact ⟨normalize_rootZeroOnly _ ih.1,normalize_cutsAvoid _ _ ih.2⟩
  | detached h hv hvr hgr hgc he ih => exact ⟨erase_rootZeroOnly _ _ _ he ih.1,erase_cutsAvoid _ _ _ _ he ih.2⟩

theorem step_selected_output (f : GTree → List Group → List RMAF.Vertex → Receipt)
    (t : GTree) (d : List Group) (c : List RMAF.Vertex) (g : Group)
    (hc : choose (normalize t) = .one g ∨ ∃ a b,
      choose (normalize t) = .two a b ∧ (g = a ∨ g = b))
    (o : Output) (ho : o ∈ (attempt f (normalize t) d c g).outputs) :
    o ∈ (step f t d c).outputs := by
  rcases hc with hc | ⟨a,b,hc,hg⟩
  · simpa [step,hc,prefixRoot] using ho
  · rcases hg with rfl | rfl
    · simp [step,hc,prefixRoot,combine,ho]
    · simp [step,hc,prefixRoot,combine,ho]

/-- Finite-budget source coverage with a genuine decreasing terminal-owner
cover. Hypotheses are ordinary source partitions, a finite representative list,
and an original-block tracking assertion; no successful output is supplied. -/
theorem run_refinement_coverage {T color t d c bs}
    (hh : History T color t d c) (hn : (leaves T).Nodup)
    (P : SourcePartition (skeleton t)) (hm : Monochromatic P id)
    (reps : List RMAF.Vertex) (hr : OwnerCover t P reps) (ht : Tracked bs t d P)
    (q : Nat) (hq : reps.length ≤ q + 1) :
    ∃ o, o ∈ (run q t d c).outputs ∧ VertexGeometry.Refines bs o.partition := by
  induction q generalizing t d c P reps with
  | zero =>
    obtain ⟨Q,hQ,hPQ⟩ := normalize_full_transport t P hm
    obtain ⟨rr,hrr,hrrlen⟩ := fullTransport_cover hPQ hr
    have htrack := tracked_normalize ht hPQ.grouped
    have hi := hh.invariant hn
    have hguards := (History.normalized hh).record_invariants
    have hnn := normalize_origins_nodup t hi.originNodup
    cases hc : choose (normalize t) with
    | finish =>
      refine ⟨⟨d.map Group.labels ++ [(groups (normalize t)).flatMap Group.labels],c⟩,?_,tracked_finish htrack⟩
      simp [run,step,hc]
    | one g =>
      obtain ⟨v,hv,hvr,hs⟩ := choose_one_source_singleton _ hnn Q hQ g hc
      obtain ⟨u,hu,QQ,hQQ,e,hlift,hsurv,habs⟩ := erase_leaf_source_transport _ hnn v g hv hvr Q hQ hs
      obtain ⟨rrr,hrrr,hlen⟩ := erase_owner_cover hrr hv hs e hlift hsurv habs
      have hpos : 0 < rrr.length := List.length_pos_iff.2 (ownerCover_nonempty hrrr)
      have hbase : rr.length ≤ 1 := by omega
      omega
    | two a b =>
      obtain ⟨v,g,hg,hv,hvr,hs⟩ := choose_two_source_singleton _ Q hQ a b hc
      obtain ⟨u,hu,QQ,hQQ,e,hlift,hsurv,habs⟩ := erase_leaf_source_transport _ hnn v g hv hvr Q hQ hs
      obtain ⟨rrr,hrrr,hlen⟩ := erase_owner_cover hrr hv hs e hlift hsurv habs
      have hpos : 0 < rrr.length := List.length_pos_iff.2 (ownerCover_nonempty hrrr)
      have hbase : rr.length ≤ 1 := by omega
      omega
    | refuse why => exact False.elim (choose_normalized_no_refusal _ (normalize_fullyNormalized t) why hc)
  | succ q ih =>
    obtain ⟨Q,hQ,hPQ⟩ := normalize_full_transport t P hm
    obtain ⟨rr,hrr,hrrlen⟩ := fullTransport_cover hPQ hr
    have htrack := tracked_normalize ht hPQ.grouped
    have hi := hh.invariant hn
    have hhn := History.normalized hh
    have hguards := hhn.record_invariants
    have hnn := normalize_origins_nodup t hi.originNodup
    have progress : choose (normalize t) = .finish ∨ ∃ v g,
        GroupLeafAt (normalize t) v g ∧ v ≠ [] ∧ SingletonBlock Q v ∧
        (choose (normalize t) = .one g ∨ ∃ a b, choose (normalize t) = .two a b ∧ (g = a ∨ g = b)) := by
      cases hc : choose (normalize t) with
      | finish => exact Or.inl rfl
      | one g =>
        obtain ⟨v,hv,hvr,hs⟩ := choose_one_source_singleton _ hnn Q hQ g hc
        exact Or.inr ⟨v,g,hv,hvr,hs,Or.inl rfl⟩
      | two a b =>
        obtain ⟨v,g,hg,hv,hvr,hs⟩ := choose_two_source_singleton _ Q hQ a b hc
        exact Or.inr ⟨v,g,hv,hvr,hs,Or.inr ⟨a,b,rfl,hg⟩⟩
      | refuse why => exact False.elim (choose_normalized_no_refusal _ (normalize_fullyNormalized t) why hc)
    rcases progress with hfinish | ⟨v,g,hv,hvr,hs,hselected⟩
    · refine ⟨⟨d.map Group.labels ++ [(groups (normalize t)).flatMap Group.labels],c⟩,?_,tracked_finish htrack⟩
      simp [run,step,hfinish]
    · obtain ⟨u,hu,ha,hun,huz,huc,QQ,hQQ,e,hlift,hsurv,habs⟩ :=
        attempt_singleton_source (run q) _ d c hnn hguards.1 hguards.2 Q hQ v g hv hvr hs
      obtain ⟨rrr,hrrr,hlen⟩ := erase_owner_cover hrr hv hs e hlift hsurv habs
      have htr := tracked_erase htrack hv hs e hlift hsurv
      have hsorigin := hhn.selected hn hv
      have hgr := groupLeaf_origin_nonempty _ hguards.1 v g hv hvr
      have hgc : g.origin ∉ c := by intro hg; exact hsorigin.2.1 g.origin hg List.prefix_rfl
      have hchild : History T color u (g :: d) (g.origin :: c) := .detached hhn hv hvr hgr hgc hu
      obtain ⟨o,ho,href⟩ := ih hchild QQ hQQ rrr hrrr htr (by omega)
      refine ⟨o,?_,href⟩
      apply step_selected_output (run q) t d c g hselected o
      rw [ha]
      exact ho

end Universal233.CutRealization
