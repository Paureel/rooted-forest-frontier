import ScalarEnvelope
namespace Universal233.Rule5LocalWork
open RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller RestrictionBridge

def commonPolynomial (N K : Nat) : Nat :=
 9*N+((8*(N+2)^2+2)*N+2)*N+7+(K+2*(2*N+2)+2)*(N*N)

theorem reconstruct_polynomial (check : Forest→Measured Bool) (d : Setup) (FX FY FM FN : Forest)
 (N K : Nat) (hx : d.X.length≤N) (hy : d.Y.length≤N)
 (hFX : cells FX≤N) (hFY : cells FY≤N) (hFM : cells FM≤N) (hFN : cells FN≤N)
 (checker : ∀G,G∈mergeCandidates d.X d.Y d.x d.y d.rho d.gamma FM FN →(check G).work≤K) :
 (reconstructMeter check d FX FY FM FN).work≤commonPolynomial N K := by
 have base:=reconstruct_work check d FX FY FM FN N K hx hy hFX hFY hFM hFN checker
 have flen : FM.length≤N := by unfold cells at hFM;omega
 have nlen : FN.length≤N := by unfold cells at hFN;omega
 have pp:=Nat.mul_le_mul flen nlen
 have bill:=Nat.mul_le_mul_left (K+2*(2*N+2)+2) pp
 unfold commonPolynomial
 omega

/-- Real stable/unstable reconstruction, with all FOUR payload domains derived
from the closed ordinary solver and actual found-one/outside programs. -/
theorem actual_common_reconstruct_polynomial (d : Setup) (r : Nat) {FX FY FM FN : Forest}
 (fx : actual d.tx d.sx r=some FX) (fm : actual d.mxT d.mxS r=some FM) {p : RMAF.Vertex}
 (pre : DepthOne.pretest01 d.ty d.sy=.found (some p))
 (fy : FY=DepthOne.forest d.sy (some p)) (fn : outsideReply d FY=some FN)
 (check : Forest→Measured Bool) (K : Nat)
 (primitive : ∀G,cells G≤12*(leaves d.T).length+1 →(check G).work≤K) :
 (reconstructMeter check d FX FY FM FN).work≤commonPolynomial (2*(leaves d.T).length) K := by
 have mn:=common_real_payload d r fm pre fy fn
 have xp:=closed_payload d.tx d.sx r (ordinary_pair_proper d) fx
 have xs:=Rule5ActualTrace.restricted_size d.nt d.htx
 have yp:=found_one_minimum d.ty d.sy p pre
 have yf:=agreement_payload d.ty d.sy (DepthOne.forest d.sy (some p))
   (restricted_nodup d.T d.ty d.Y d.hty d.nt) yp.1
 have ys:=Rule5ActualTrace.restricted_size d.nt d.hty
 have blocks:=setup_blocks d
 apply reconstruct_polynomial check d FX FY FM FN (2*(leaves d.T).length) K
   (by omega) (by omega) (by omega) (by rw [fy];omega) mn.1 mn.2
 intro G hg
 have payload:=merge_payload d.X d.Y d.x d.y d.rho d.gamma FM FN
   (2*(leaves d.T).length) mn.1 mn.2 (by rw [merge_value];exact hg)
 apply primitive G
 omega
end Universal233.Rule5LocalWork
