import PaidDefs
namespace OrdinaryCommonSplit.Caller
open RMAF RestrictionBridge

theorem ordinary_inside_debt (d : Setup) (hn : IsMinimum d.ty d.sy 1)
    (F : Forest) (ha : agreement d.T d.S F=true) :
    agreement d.tx d.sx (clip d.X F)=true ∧ (clip d.X F).length-1+1≤F.length-1 := by
  have ax := (agreement_clip d.T d.S d.tx d.sx d.X F d.htx d.hsx ha).1
  have ay := (agreement_clip d.T d.S d.ty d.sy d.Y F d.hty d.hsy ha).1
  have low := hn.2 _ ay
  have count := actual_split_clip_bound d.T d.S d.X d.Y F d.nt d.hpT d.edgeT ha
  have px := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty d.tx d.sx _ ax)
  have py := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty d.ty d.sy _ ay)
  exact ⟨ax,by omega⟩

/-- Feasibility of the actual marked inside query at q-1 is derived from an
original feasible AF, not from a free budget discount or a supplied marked
minimum. At the tight boundary the proof uses the actual crossing projection. -/
theorem marked_inside_feasible (d : Setup) (m q : Nat)
    (hm : IsMinimum d.tx d.sx m) (hn : IsMinimum d.ty d.sy 1)
    (F : Forest) (ha : agreement d.T d.S F=true) (hq : F.length-1≤q) :
    ∃G,agreement d.mxT d.mxS G=true ∧ G.length-1≤q-1 := by
  have low := original_sum_lower d.T d.S d.tx d.sx d.ty d.sy d.X d.Y m 1
    d.nt d.hpT d.edgeT d.htx d.hsx d.hty d.hsy hm hn F ha
  by_cases roomy : m+2≤q
  · obtain ⟨FX,aFX,cFX⟩ := hm.1
    have subXT : d.X⊆leaves d.T := fun _ hz => (split_labels _ d.X d.Y d.hpT _).2 (Or.inl hz)
    have subXS : d.X⊆leaves d.S := fun _ hz => (split_labels _ d.X d.Y d.hpS _).2 (Or.inl hz)
    have subYT : d.Y⊆leaves d.T := fun _ hz => (split_labels _ d.X d.Y d.hpT _).2 (Or.inr hz)
    have subYS : d.Y⊆leaves d.S := fun _ hz => (split_labels _ d.X d.Y d.hpS _).2 (Or.inr hz)
    obtain ⟨G,aG,cG⟩ := marked_extension d.T d.S d.tx d.sx d.mxT d.mxS d.X d.y d.rho
      d.nt d.ns (checked_block_nodup _ _ d.hpT d.X (by simp)) subXT subXS (subYT d.hy) (subYS d.hy)
      (by intro hyx;exact split_disjoint _ d.X d.Y d.hpT d.y hyx d.hy)
      d.htx d.hsx d.hMXT d.hMXS FX aFX
    have pos := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty d.tx d.sx FX aFX)
    exact ⟨G,aG,by omega⟩
  · have eq : F.length-1=m+1 := by omega
    have ax := (agreement_clip d.T d.S d.tx d.sx d.X F d.htx d.hsx ha).1
    have ay := (agreement_clip d.T d.S d.ty d.sy d.Y F d.hty d.hsy ha).1
    have lx := hm.2 _ ax
    have ly := hn.2 _ ay
    have px := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty d.tx d.sx _ ax)
    have py := List.length_pos_iff.2 (Universal233.DepthOne.agreement_nonempty d.ty d.sy _ ay)
    have count := actual_split_clip_bound d.T d.S d.X d.Y F d.nt d.hpT d.edgeT ha
    obtain ⟨B,hB,nX,nY⟩ := equal_sum_has_crossing d.T d.S d.tx d.sx d.ty d.sy d.X d.Y m 1
      d.hpT d.htx d.hsx d.hty d.hsy hm hn F ha eq
    obtain ⟨G,aG,cG⟩ := arbitrary_original_marked_projection d.T d.S d.mxT d.mxS d.X d.Y B F d.y d.rho
      d.nt d.ns d.hpT d.hpS d.edgeT d.edgeS hB nX nY d.hy d.frT d.frS d.hMXT d.hMXS ha
    exact ⟨G,aG,by omega⟩
end OrdinaryCommonSplit.Caller
