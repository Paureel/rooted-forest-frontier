import CheckedMerge
namespace Universal233.Rule5LocalWork
open RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller

theorem proper_left_nodup {T S : Tree} (hp : DepthOne.proper T S=true) : (leaves T).Nodup := by
 simp only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at hp
 exact hp.1.1

theorem setup_blocks (d : Setup) : d.X.length+d.Y.length=(leaves d.T).length := by
 have h:([d.X,d.Y]:Forest).flatten.Perm (leaves d.T) :=
   FinalCutRecovery.checked_flatten_perm d.T [d.X,d.Y] d.nt d.hpT
 have len:=h.length_eq
 simpa using len

/-- Actual closed marked callback and actual depth-one outside reply. The
outside payload bound follows from its proved agreement, even on the explicit
cost-two extension branch; no hostile arbitrary callback premise. -/
theorem common_real_payload (d : Setup) (r : Nat) {FM FY FN : Forest}
 (fm : actual d.mxT d.mxS r=some FM) {p : RMAF.Vertex}
 (pre : DepthOne.pretest01 d.ty d.sy=.found (some p))
 (fy : FY=DepthOne.forest d.sy (some p)) (fn : outsideReply d FY=some FN) :
 cells FM≤2*(leaves d.T).length ∧ cells FN≤2*(leaves d.T).length := by
 have mp := marked_pair_setup_proper d
 have mf := closed_payload d.mxT d.mxS r mp fm
 have msize := Rule5ActualTrace.marked_size d.nt d.hMXT
 have found := found_one_minimum d.ty d.sy p pre
 subst FY
 obtain ⟨F,out,aF,_,_⟩ := outsideReply_spec d _ found.1 found.2.1
 have eq : F=FN := Option.some.inj (out.symm.trans fn)
 have outside := agreement_payload d.myT d.myS F (proper_left_nodup (marked_outside_proper d)) aF
 have nsize := Rule5ActualTrace.marked_size d.nt d.hMYT
 subst F
 omega

/-- The real common-one merge call has a polynomial outer bill in n plus the
primitive actual-agreement bill K on all generated inputs. The payload premise
for K is discharged below, including failed and duplicate owner guesses. -/
theorem common_real_pick_work (d : Setup) (r : Nat) {FM FY FN : Forest}
 (fm : actual d.mxT d.mxS r=some FM) {p : RMAF.Vertex}
 (pre : DepthOne.pretest01 d.ty d.sy=.found (some p))
 (fy : FY=DepthOne.forest d.sy (some p)) (fn : outsideReply d FY=some FN)
 (check : Forest→Measured Bool) (K : Nat)
 (primitive : ∀G,cells G≤12*(leaves d.T).length+1 →(check G).work≤K) :
 (pickMeter check d.X d.Y d.x d.y d.rho d.gamma FM FN).work≤
 let N:=2*(leaves d.T).length
 4*N+((8*(N+2)^2+2)*N+2)*N+2+(K+2*(2*N+2)+2)*(FM.length*FN.length) := by
 have pay := common_real_payload d r fm pre fy fn
 have blocks:=setup_blocks d
 apply pick_work check d.X d.Y d.x d.y d.rho d.gamma FM FN (2*(leaves d.T).length) K
   (by omega) (by omega) pay.1 pay.2
 intro G hg
 have bound:=merge_payload d.X d.Y d.x d.y d.rho d.gamma FM FN
   (2*(leaves d.T).length) pay.1 pay.2 (by rw [merge_value];exact hg)
 apply primitive G
 omega

def reconstructMeter (check : Forest→Measured Bool) (d : Setup) (FX FY FM FN : Forest) : Measured (Option Forest) :=
 let guards:=FX.length+FY.length+FM.length+FN.length+4
 if FM.length-1=FX.length-1 ∧ FN.length-1=FY.length-1 then
  let m:=pickMeter check d.X d.Y d.x d.y d.rho d.gamma FM FN
  ⟨m.value,guards+m.work⟩
 else ⟨some (FX++FY),guards+FX.length+1⟩

theorem reconstruct_value (check : Forest→Measured Bool) (d : Setup) (FX FY FM FN : Forest)
 (primitive : ∀G,G∈mergeCandidates d.X d.Y d.x d.y d.rho d.gamma FM FN →
    (check G).value=agreement d.T d.S G) :
 (reconstructMeter check d FX FY FM FN).value=reconstruct d FX FY FM FN := by
 simp only [reconstructMeter,reconstruct]
 split
 · exact pick_value d.T d.S check _ _ _ _ _ _ _ _ primitive
 · rfl

theorem reconstruct_work (check : Forest→Measured Bool) (d : Setup) (FX FY FM FN : Forest)
 (N K : Nat) (hx : d.X.length≤N) (hy : d.Y.length≤N)
 (hFX : cells FX≤N) (hFY : cells FY≤N) (hFM : cells FM≤N) (hFN : cells FN≤N)
 (checker : ∀G,G∈mergeCandidates d.X d.Y d.x d.y d.rho d.gamma FM FN →(check G).work≤K) :
 (reconstructMeter check d FX FY FM FN).work≤
 9*N+((8*(N+2)^2+2)*N+2)*N+7+(K+2*(2*N+2)+2)*(FM.length*FN.length) := by
 have fxl : FX.length≤N := by unfold cells at hFX;omega
 have fyl : FY.length≤N := by unfold cells at hFY;omega
 have fml : FM.length≤N := by unfold cells at hFM;omega
 have fnl : FN.length≤N := by unfold cells at hFN;omega
 have picked:=pick_work check d.X d.Y d.x d.y d.rho d.gamma FM FN N K hx hy hFM hFN checker
 unfold reconstructMeter
 split <;> dsimp only <;> omega
end Universal233.Rule5LocalWork
