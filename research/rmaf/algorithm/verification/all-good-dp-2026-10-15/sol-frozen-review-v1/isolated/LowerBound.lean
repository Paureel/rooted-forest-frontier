import CutColoring
import Recovery

namespace AllGoodDP
open RMAF RestrictionBridge ForestState

theorem findIdx_congr_on {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ x ∈ xs, p x = q x) : xs.findIdx p = xs.findIdx q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.findIdx_cons,List.findIdx_cons,h a (by simp),ih (fun x hx => h x (by simp [hx]))]

theorem owner_source_mono (T : Option Tree) (ss : List Tree)
    (hp : proper T ss = true) (s : Tree) (hs : s ∈ ss) :
    ∀ x y, x ∈ leaves s → y ∈ leaves s → owner ss x = owner ss y := by
  have hQ := (proper_parts T ss hp).2
  intro x y hx hy
  have hsQ : leaves s ∈ ss.map leaves := List.mem_map.2 ⟨s,hs,rfl⟩
  have hxt := checked_label (labels T) (ss.map leaves) hQ hsQ hx
  have hyt := checked_label (labels T) (ss.map leaves) hQ hsQ hy
  obtain ⟨X,hX,hxX,hcX,ux⟩ := unique_label_owner (ss.map leaves) x
    (checked_count (labels T) _ hQ hxt)
  obtain ⟨Y,hY,hyY,hcY,uy⟩ := unique_label_owner (ss.map leaves) y
    (checked_count (labels T) _ hQ hyt)
  have hXs := ux (leaves s) hsQ hx
  have hYs := uy (leaves s) hsQ hy
  apply findIdx_congr_on
  intro u hu
  have huQ : leaves u ∈ ss.map leaves := List.mem_map.2 ⟨u,hu,rfl⟩
  by_cases hxu : x ∈ leaves u
  · have heu : leaves u = leaves s := (ux (leaves u) huQ hxu).trans hXs.symm
    have hyu : y ∈ leaves u := heu.symm ▸ hy
    simp [hxu,hyu]
  · have hyu : y ∉ leaves u := by
      intro hyu
      have heu : leaves u = leaves s := (uy (leaves u) huQ hyu).trans hYs.symm
      exact hxu (heu.symm ▸ hx)
    simp [hxu,hyu]

theorem agrees_parts (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (ha : agrees T ss F = true) :
    proper T ss = true ∧ partitionCheck (labels T) F = true ∧
    (∀ B ∈ F, ∃ s ∈ ss, B ⊆ leaves s) ∧ targetEmbeddings T F = true ∧
      ∀ s ∈ ss, sourceCheck T F s = true := by
  simpa only [agrees,Bool.and_eq_true,List.all_eq_true,List.any_eq_true,contained_iff,
    and_assoc] using ha

theorem agreement_owner_mono (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (ha : agrees T ss F = true) :
    ∀ B ∈ F, ∀ x y, x ∈ B → y ∈ B → owner ss x = owner ss y := by
  have hs := agrees_parts T ss F ha
  intro B hB x y hx hy
  obtain ⟨s,hsm,hBs⟩ := hs.2.2.1 B hB
  exact owner_source_mono T ss hs.1 s hsm x y (hBs hx) (hBs hy)

theorem leaf_label_mem (t : Tree) (v : Vertex) (x : Nat)
    (h : Universal233.CoreGraph.LeafAt t v x) : x ∈ leaves t := by
  induction v generalizing t with
  | nil =>
    have he : t = .leaf x := Option.some.inj h
    simp [he,leaves]
  | cons b v ih =>
    cases t with
    | leaf y => simp [Universal233.CoreGraph.LeafAt,Universal233.CoreGraph.subtree] at h
    | node l r =>
      cases b
      · have hh := ih l h; simp [leaves,hh]
      · have hh := ih r h; simp [leaves,hh]

theorem realized_walk_mono (t : Tree) (o : Universal233.CoreProgram.Output) (own : Nat → Nat)
    (hr : Universal233.CutRealization.RealizedOutput t o)
    (hm : ∀ B ∈ o.partition, ∀ x y, x ∈ B → y ∈ B → own x = own y)
    (a b : Vertex) (x y : Nat) (ha : Universal233.CoreGraph.LeafAt t a x)
    (hb : Universal233.CoreGraph.LeafAt t b y)
    (hw : Universal233.CutRealization.ResidualWalk t o.sourceCuts a b) : own x = own y := by
  obtain ⟨hgood,hcuts,C,hCf,hCs,hC,hCnd,hcover,hsep,hleaf,hcount⟩ := hr
  obtain ⟨r,hrC,hra⟩ := hcover a hw.start
  obtain ⟨p,hp,he⟩ := List.mem_map.1 hrC
  have hpr : p.1 = r := he
  have hlab := hC p.1 p.2 hp
  have hx : x ∈ p.2 := (hlab.exact a x ha).2 (hpr.symm ▸ hra)
  have hy : y ∈ p.2 := (hlab.exact b y hb).2 (hpr.symm ▸ hra.trans hw)
  have hP : p.2 ∈ o.partition := by
    rw [←hCs]
    exact List.mem_map.2 ⟨p,hp,rfl⟩
  exact hm p.2 hP x y hx hy

theorem realized_coloring (t : Tree) (o : Universal233.CoreProgram.Output)
    (cs : List Nat) (own : Nat → Nat)
    (hr : Universal233.CutRealization.RealizedOutput t o)
    (hused : ∀ x ∈ leaves t, own x ∈ cs)
    (hm : ∀ B ∈ o.partition, ∀ x y, x ∈ B → y ∈ B → own x = own y) :
    ∃ p, Valid cs own t p ∧ changes p ≤ o.sourceCuts.length := by
  classical
  have hleaf := hr.2.2.choose_spec.2.2.2.2.2.2.1
  have hex : ∀ v, Universal233.CoreGraph.Valid t v →
      ∃ w : Vertex × Nat, Universal233.CoreGraph.LeafAt t w.1 w.2 ∧
        Universal233.CutRealization.ResidualWalk t o.sourceCuts v w.1 := by
    intro v hv
    obtain ⟨a,x,ha,hw⟩ := hleaf v hv
    exact ⟨(a,x),ha,hw⟩
  let pick := fun v hv => Classical.choose (hex v hv)
  have hpick := fun v hv => Classical.choose_spec (hex v hv)
  let f := fun v => if hv : Universal233.CoreGraph.Valid t v then own (pick v hv).2 else 0
  have hf : ∀ v hv, f v = own (pick v hv).2 := by intro v hv; simp [f,hv]
  have hfc : ∀ v, Universal233.CoreGraph.Valid t v → f v ∈ cs := by
    intro v hv
    rw [hf v hv]
    exact hused _ (leaf_label_mem t _ _ (hpick v hv).1)
  have hfl : ∀ v x, Universal233.CoreGraph.LeafAt t v x → f v = own x := by
    intro v x hx
    have hv : Universal233.CoreGraph.Valid t v := ⟨_,hx⟩
    rw [hf v hv]
    exact (realized_walk_mono t o own hr hm v (pick v hv).1 x (pick v hv).2
      hx (hpick v hv).1 (hpick v hv).2).symm
  have hconst : ∀ v e, Universal233.CutRealization.ResidualAdj t o.sourceCuts v e → f v = f e := by
    intro v e he
    rw [hf v he.1.1,hf e he.1.2.1]
    have hpath := (hpick v he.1.1).2.reverse.trans
      (Universal233.CutRealization.ResidualWalk.step he (hpick e he.1.2.1).2)
    exact realized_walk_mono t o own hr hm _ _ _ _ (hpick v he.1.1).1
      (hpick e he.1.2.1).1 hpath
  exact ⟨shade t f,shade_valid t f cs own hfc hfl,shade_cut_bound t o.sourceCuts f hconst⟩

theorem agreement_coloring (t : Tree) (ss : List Tree) (F : List (List Nat))
    (ha : agrees (some t) ss F = true) :
    ∃ p, Valid (List.range ss.length) (owner ss) t p ∧ changes p ≤ F.length - 1 := by
  have hs := agrees_parts (some t) ss F ha
  have hn := (proper_parts (some t) ss hs.1).1
  obtain ⟨o,ho,hgen,hcost,hlen,hreal,hperm,hcheck⟩ :=
    Universal233.FinalCutRecovery.recover_checked t F hn hs.2.1 hs.2.2.2.1
  have hmF := agreement_owner_mono (some t) ss F ha
  have hm : ∀ B ∈ o.partition, ∀ x y, x ∈ B → y ∈ B → owner ss x = owner ss y := by
    obtain ⟨f,hfperm,hf⟩ := hperm
    intro B hB x y hx hy
    have hfB : f B ∈ F := hfperm.mem_iff.1 (List.mem_map.2 ⟨B,hB,rfl⟩)
    exact hmF (f B) hfB x y ((hf B hB).mem_iff.2 hx) ((hf B hB).mem_iff.2 hy)
  obtain ⟨p,hp,hbound⟩ := realized_coloring t o (List.range ss.length) (owner ss) hreal
    (fun x hx => List.mem_range.2 (owner_lt (some t) ss hs.1 x hx)) hm
  exact ⟨p,hp,by omega⟩

end AllGoodDP
