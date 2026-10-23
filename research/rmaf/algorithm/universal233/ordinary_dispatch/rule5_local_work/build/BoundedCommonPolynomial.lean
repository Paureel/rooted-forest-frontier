import CommonPolynomial
namespace Universal233.Rule5LocalWork
open RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source RestrictionBridge

/-- Bit-aware checker domain: only actual bounded numeric payloads are required.
The input L-bit premise and BOTH checked payload bounds are discharged from
actual source build / closed callbacks, even for failing merge candidates. -/
theorem actual_common_bounded_polynomial (T S : Tree) (X Y : List Nat) (edge : RMAF.Vertex)
 (d : Setup) (build : buildSetup T S X Y edge=some d) (r : Nat) {FX FY FM FN : Forest}
 (fx : actual d.tx d.sx r=some FX) (fm : actual d.mxT d.mxS r=some FM) {p : RMAF.Vertex}
 (pre : DepthOne.pretest01 d.ty d.sy=.found (some p))
 (fy : FY=DepthOne.forest d.sy (some p)) (fn : outsideReply d FY=some FN)
 (L : Nat) (labels : ∀z,z∈leaves T++leaves S →z<2^L)
 (check : Forest→Measured Bool) (K : Nat)
 (primitive : ∀G,cells G≤12*(leaves d.T).length+1 →
    (∀z,z∈G.flatten →z<2^(L+2)) →(check G).work≤K) :
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
 apply primitive G (by omega)
 exact common_real_bits T S X Y edge d build r fm pre fy fn hg L labels
end Universal233.Rule5LocalWork
