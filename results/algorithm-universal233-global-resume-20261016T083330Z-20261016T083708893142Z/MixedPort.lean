import PortSingleton
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

theorem rootedIso_refl (t : Tree) : RootedIso t t := (sameShape_correct t t).1 (sameShape_refl t)

theorem rootedIso_trans {t s : Tree} (h : RootedIso t s) {u : Tree}
    (g : RootedIso s u) : RootedIso t u := by
  induction h generalizing u with
  | leaf x => exact g
  | straight h1 h2 ih1 ih2 =>
    cases g with
    | straight g1 g2 => exact .straight (ih1 g1) (ih2 g2)
    | swapped g1 g2 => exact .swapped (ih1 g1) (ih2 g2)
  | swapped h1 h2 ih1 ih2 =>
    cases g with
    | straight g1 g2 => exact .swapped (ih1 g2) (ih2 g1)
    | swapped g1 g2 => exact .straight (ih1 g2) (ih2 g1)

/-- The opposite rooted orientations need both actual marked comparisons.
Each forces the other attachment to a root join in the selected component;
substitution then reconstructs the same original union up to child swap. -/
theorem mixed_port_topology_glue (c d : Port) (uY uX vY vX : Tree)
    (K L : List Nat) (x y : Nat)
    (ndT : (leaves (c.plug uY)).Nodup) (ndS : (leaves (d.plug uX)).Nodup)
    (hK : K⊆leaves uX) (hL : L⊆leaves uY)
    (sepYK : ∀ z∈leaves uY, z∉K) (sepXL : ∀ z∈leaves uX, z∉L)
    (hxC : x∈c.labels) (hxX : x∈leaves uX)
    (hyD : y∈d.labels) (hyY : y∈leaves uY)
    (hvX : restrict K uX=some vX) (hvY : restrict L uY=some vY)
    (hmarkX : restrictionAgrees (c.plug uY) (d.plug uX) (K++[y])=true)
    (hmarkY : restrictionAgrees (c.plug uY) (d.plug uX) (L++[x])=true) :
    restrictionAgrees (c.plug uY) (d.plug uX) (K++L)=true := by
  have nT := List.nodup_append.1 ((c.leaves_perm uY).nodup_iff.1 ndT)
  have nS := List.nodup_append.1 ((d.leaves_perm uX).nodup_iff.1 ndS)
  have sepC : ∀ z∈leaves uY, z∉c.labels := by
    intro z hz hc
    exact nT.2.2 z hc z hz rfl
  have sepD : ∀ z∈leaves uX, z∉d.labels := by
    intro z hz hd
    exact nS.2.2 z hd z hz rfl
  have hLout : ∀ z∈c.labels, z∉L := by
    intro z hz hzl;exact sepC z (hL hzl) hz
  have hKout : ∀ z∈d.labels, z∉K := by
    intro z hz hzk;exact sepD z (hK hzk) hz
  have hyC : y∉c.labels := sepC y hyY
  have hxD : x∉d.labels := sepD x hxX
  have hyX : y∉leaves uX := by intro hy;exact sepD y hy hyD
  have hxY : x∉leaves uY := by intro hx;exact sepC x hx hxC
  have hTmX : restrict (K++[y]) (c.plug uY)=some ((c.clip K).plug (.leaf y)) :=
    c.restrict_join uY (.leaf y) K [y] sepYK
      (by
        intro z hz hzy
        have he : z=y := by simpa using hzy
        subst z
        exact hyC hz)
      (restrict_singleton uY y nT.2.1 hyY)
  obtain ⟨wSX,hwSX,hiSX⟩ := d.one_outside_projection uX vX K y nS.1 hyD hyX hK sepD hvX
  have hiX : RootedIso ((c.clip K).plug (.leaf y)) (.node vX (.leaf y)) := by
    have ht : RootedIso ((c.clip K).plug (.leaf y)) wSX := by
      apply (sameShape_correct _ _).1
      simpa only [restrictionAgrees,hTmX,hwSX] using hmarkX
    exact rootedIso_trans ht hiSX
  have hSmY : restrict (L++[x]) (d.plug uX)=some ((d.clip L).plug (.leaf x)) :=
    d.restrict_join uX (.leaf x) L [x] sepXL
      (by
        intro z hz hzx
        have he : z=x := by simpa using hzx
        subst z
        exact hxD hz)
      (restrict_singleton uX x nS.2.1 hxX)
  obtain ⟨wTY,hwTY,hiTY⟩ := c.one_outside_projection uY vY L x nT.1 hxC hxY hL sepC hvY
  have hiY : RootedIso ((d.clip L).plug (.leaf x)) (.node vY (.leaf x)) := by
    have ht : RootedIso wTY ((d.clip L).plug (.leaf x)) := by
      apply (sameShape_correct _ _).1
      simpa only [restrictionAgrees,hwTY,hSmY] using hmarkY
    exact rootedIso_trans (BinaryExchange.iso_symm ht) hiTY
  have nyvX : y∉leaves vX := fun h => hyX ((restricted_labels_exact uX vX K hvX).1 h).1
  have nxvY : x∉leaves vY := fun h => hxY ((restricted_labels_exact uY vY L hvY).1 h).1
  have hTglue : RootedIso ((c.clip K).plug vY) (.node vX vY) := by
    have hh := graft_iso y vY vY _ _ (rootedIso_refl vY) hiX
    rw [Port.graft_hole (c.clip K) y vY (fun h => hyC (c.clip_labels_sub K h))] at hh
    simpa only [graft,graft_absent y vY vX nyvX,ite_true] using hh
  have hSglue : RootedIso ((d.clip L).plug vX) (.node vY vX) := by
    have hh := graft_iso x vX vX _ _ (rootedIso_refl vX) hiY
    rw [Port.graft_hole (d.clip L) x vX (fun h => hxD (d.clip_labels_sub L h))] at hh
    simpa only [graft,graft_absent x vX vY nxvY,ite_true] using hh
  have hTunion : restrict (K++L) (c.plug uY)=some ((c.clip K).plug vY) :=
    c.restrict_join uY vY K L sepYK hLout hvY
  have hSunion : restrict (K++L) (d.plug uX)=some ((d.clip L).plug vX) := by
    have hcomm : restrict (K++L) (d.plug uX)=restrict (L++K) (d.plug uX) :=
      Universal233.DepthOne.restrict_members _ _ _ (by intro z;simp only [List.mem_append];exact or_comm)
    exact hcomm.trans (d.restrict_join uX vX L K sepXL hKout hvX)
  have hswap : RootedIso (.node vX vY) (.node vY vX) :=
    .swapped (rootedIso_refl vX) (rootedIso_refl vY)
  have hfinal := rootedIso_trans hTglue (rootedIso_trans hswap (BinaryExchange.iso_symm hSglue))
  simpa only [restrictionAgrees,hTunion,hSunion] using (sameShape_correct _ _).2 hfinal
end OrdinaryCommonSplit
