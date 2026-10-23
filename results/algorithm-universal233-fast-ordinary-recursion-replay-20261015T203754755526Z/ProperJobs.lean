import PaidExact
namespace OrdinaryCommonSplit.Caller
open RMAF RestrictionBridge Universal233

theorem ordinary_pair_proper (d : Setup) : DepthOne.proper d.tx d.sx=true := by
  have nx := checked_block_nodup _ _ d.hpT d.X (by simp)
  have sT : d.X⊆leaves d.T := fun _ h => (split_labels _ d.X d.Y d.hpT _).2 (Or.inl h)
  have sS : d.X⊆leaves d.S := fun _ h => (split_labels _ d.X d.Y d.hpS _).2 (Or.inl h)
  have pT := restricted_perm d.T d.tx d.X d.htx d.nt nx sT
  have pS := restricted_perm d.S d.sx d.X d.hsx d.ns nx sS
  exact (DepthOne.proper_iff _ _).2 ⟨pT.nodup_iff.2 nx,pS.nodup_iff.2 nx,pT.trans pS.symm⟩

theorem marked_pair_setup_proper (d : Setup) : DepthOne.proper d.mxT d.mxS=true := by
  have nx := checked_block_nodup _ _ d.hpT d.X (by simp)
  have sXT : d.X⊆leaves d.T := fun _ h => (split_labels _ d.X d.Y d.hpT _).2 (Or.inl h)
  have sXS : d.X⊆leaves d.S := fun _ h => (split_labels _ d.X d.Y d.hpS _).2 (Or.inl h)
  have sYT : d.Y⊆leaves d.T := fun _ h => (split_labels _ d.X d.Y d.hpT _).2 (Or.inr h)
  have sYS : d.Y⊆leaves d.S := fun _ h => (split_labels _ d.X d.Y d.hpS _).2 (Or.inr h)
  obtain ⟨t,s,ht,hs,hp,_,_⟩ := marked_pair_proper d.T d.S d.X d.y d.rho
    d.nt d.ns nx (sYT d.hy) (sYS d.hy)
    (by intro h;exact split_disjoint _ d.X d.Y d.hpT d.y h d.hy) sXT sXS d.frT d.frS
  have et : t=d.mxT := Option.some.inj (ht.symm.trans d.hMXT)
  have es : s=d.mxS := Option.some.inj (hs.symm.trans d.hMXS)
  simpa only [et,es] using hp

theorem marked_outside_proper (d : Setup) : DepthOne.proper d.myT d.myS=true := by
  have ny := checked_block_nodup _ _ d.hpT d.Y (by simp)
  have sXT : d.X⊆leaves d.T := fun _ h => (split_labels _ d.X d.Y d.hpT _).2 (Or.inl h)
  have sXS : d.X⊆leaves d.S := fun _ h => (split_labels _ d.X d.Y d.hpS _).2 (Or.inl h)
  have sYT : d.Y⊆leaves d.T := fun _ h => (split_labels _ d.X d.Y d.hpT _).2 (Or.inr h)
  have sYS : d.Y⊆leaves d.S := fun _ h => (split_labels _ d.X d.Y d.hpS _).2 (Or.inr h)
  obtain ⟨t,s,ht,hs,hp,_,_⟩ := marked_pair_proper d.T d.S d.Y d.x d.gamma
    d.nt d.ns ny (sXT d.hx) (sXS d.hx)
    (split_disjoint _ d.X d.Y d.hpT d.x d.hx) sYT sYS d.fgT d.fgS
  have et : t=d.myT := Option.some.inj (ht.symm.trans d.hMYT)
  have es : s=d.myS := Option.some.inj (hs.symm.trans d.hMYS)
  simpa only [et,es] using hp

theorem actual_job_progress (d : Setup) (q : Nat) (j : Job) (hj : j∈paidJobs d q) :
    DepthOne.proper j.T j.S=true ∧ j.budget<q ∧ q-j.budget=1 := by
  by_cases zero : q=0
  · simp [paidJobs,zero] at hj
  · have jobs : j=⟨d.tx,d.sx,q-1⟩ ∨ j=⟨d.mxT,d.mxS,q-1⟩ := by simpa [paidJobs,zero] using hj
    rcases jobs with rfl | rfl
    · exact ⟨ordinary_pair_proper d,by simp only;omega,by simp only;omega⟩
    · exact ⟨marked_pair_setup_proper d,by simp only;omega,by simp only;omega⟩
end OrdinaryCommonSplit.Caller
