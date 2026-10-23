import OutsideDefs
namespace OrdinaryCommonSplit.Caller
open RMAF RestrictionBridge Universal233

theorem outsideExtension_spec (d : Setup) (FY : Forest)
    (aFY : agreement d.ty d.sy FY=true) (cFY : FY.length-1=1) :
    agreement d.myT d.myS (outsideExtension d FY)=true ∧ (outsideExtension d FY).length-1=2 := by
  have ny := checked_block_nodup _ _ d.hpT d.Y (by simp)
  have sXT : d.X⊆leaves d.T := fun _ h => (split_labels _ d.X d.Y d.hpT _).2 (Or.inl h)
  have sXS : d.X⊆leaves d.S := fun _ h => (split_labels _ d.X d.Y d.hpS _).2 (Or.inl h)
  have sYT : d.Y⊆leaves d.T := fun _ h => (split_labels _ d.X d.Y d.hpT _).2 (Or.inr h)
  have sYS : d.Y⊆leaves d.S := fun _ h => (split_labels _ d.X d.Y d.hpS _).2 (Or.inr h)
  have ext := literal_marked_extension d.T d.S d.ty d.sy d.myT d.myS d.Y d.x d.gamma
    d.nt d.ns ny sYT sYS (sXT d.hx) (sXS d.hx)
    (split_disjoint _ d.X d.Y d.hpT d.x d.hx) d.hty d.hsy d.hMYT d.hMYS FY aFY
  have pos := List.length_pos_iff.2 (DepthOne.agreement_nonempty d.ty d.sy FY aFY)
  exact ⟨ext.1,by change (relabelForest (swap d.x d.gamma) ([d.x]::FY)).length-1=2;omega⟩

/-- Actual polynomial depth01 test, with its rejected branch bound to the
actual explicit cost-two extension. No depth-two or exact small oracle. -/
theorem outsideReply_spec (d : Setup) (FY : Forest)
    (aFY : agreement d.ty d.sy FY=true) (cFY : FY.length-1=1) :
    ∃ FN,outsideReply d FY=some FN ∧ agreement d.myT d.myS FN=true ∧
      IsMinimum d.myT d.myS (FN.length-1) ∧ FN.length-1≤2 := by
  cases hp : DepthOne.pretest01 d.myT d.myS with
  | refused =>
    have bad := (DepthOne.refused_iff d.myT d.myS).1 hp
    have good := marked_outside_proper d
    simp [good] at bad
  | found c =>
    obtain ⟨a,cost,min⟩ := DepthOne.found_globally_minimum d.myT d.myS c hp
    refine ⟨DepthOne.forest d.myS c,by simp [outsideReply,hp],a,⟨⟨_,a,rfl⟩,?_⟩,?_⟩
    · intro G aG
      rw [cost]
      exact min G aG
    · rw [cost]
      have := DepthOne.cutCost_le_one c
      omega
  | rejected =>
    obtain ⟨a,cost⟩ := outsideExtension_spec d FY aFY cFY
    have low := DepthOne.rejected_lower_bound d.myT d.myS hp
    refine ⟨outsideExtension d FY,by simp [outsideReply,hp],a,⟨⟨_,a,rfl⟩,?_⟩,by omega⟩
    intro G aG
    rw [cost]
    exact low G aG

theorem runWithOutside_exact (d : Setup) (q : Nat) (FY : Forest)
    (cb : Tree→Tree→Nat→Option Forest)
    (aFY : agreement d.ty d.sy FY=true) (cFY : FY.length-1=1)
    (hn : IsMinimum d.ty d.sy 1) (ih : ActualIH d q cb) :
    BoundedExact d.T d.S q (runWithOutside d q FY cb) := by
  obtain ⟨FN,hFN,aFN,hg,cFN⟩ := outsideReply_spec d FY aFY cFY
  simp only [runWithOutside,hFN]
  exact runPaid_exact d q FY FN cb aFY cFY hn aFN hg ih
end OrdinaryCommonSplit.Caller
