import CandidateNumeric
namespace Universal233.Rule5LocalWork
open RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source

def inputMax (T S : Tree) : Nat := labelMax (leaves T++leaves S)

theorem input_bits (T S : Tree) (L : Nat)
 (labels : ∀x,x∈leaves T++leaves S →x<2^L) : inputMax T S<2^L := by
 have positive : 1≤2^L := Nat.one_le_pow _ _ (by decide)
 have cap : labelMax (leaves T++leaves S)≤2^L-1 :=
   labelMax_cap _ _ (fun x hx=>by have:=labels x hx;omega)
 unfold inputMax
 omega

theorem fresh_two_bits (M L : Nat) (input : M<2^L) : M+2<2^(L+2) := by
 have positive : 1≤2^L := Nat.one_le_pow _ _ (by decide)
 rw [Nat.pow_add]
 simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one]
 omega

/-- Actual common checker labels fit L+2 bits if both original input trees
fit L bits. This deliberately conservative bit cap needs no unit scalar model. -/
theorem common_real_bits (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (d : Setup)
 (build : buildSetup T S X Y p=some d) (r : Nat) {FM FY FN : Forest}
 (fm : actual d.mxT d.mxS r=some FM) {e : RMAF.Vertex}
 (pre : DepthOne.pretest01 d.ty d.sy=.found (some e))
 (fy : FY=DepthOne.forest d.sy (some e)) (fn : outsideReply d FY=some FN)
 {G : Forest} (mem : G∈mergeCandidates d.X d.Y d.x d.y d.rho d.gamma FM FN)
 (L : Nat) (labels : ∀x,x∈leaves T++leaves S →x<2^L) :
 ∀z,z∈G.flatten →z<2^(L+2) := by
 have cap:=common_real_numeric T S X Y p d build r fm pre fy fn mem
 have old:=input_bits T S L labels
 have fresh:=fresh_two_bits (inputMax T S) L old
 intro z hz
 have hzcap:=cap z hz
 unfold inputMax at fresh
 omega

/-- Converts the structural companion's scan/constructor counts at an explicit
primitive scalar fee. It is conditional only on that separate primitive model,
not a desired whole-caller bill. -/
def scaledWork (fee : Nat) {α : Type} (r : Measured α) : Nat := fee*r.work

theorem reconstruct_scaled (fee : Nat) (check : Forest→Measured Bool) (d : Setup)
 (FX FY FM FN : Forest) (N K : Nat) (hx : d.X.length≤N) (hy : d.Y.length≤N)
 (hFX : cells FX≤N) (hFY : cells FY≤N) (hFM : cells FM≤N) (hFN : cells FN≤N)
 (checker : ∀G,G∈mergeCandidates d.X d.Y d.x d.y d.rho d.gamma FM FN →(check G).work≤K) :
 scaledWork fee (reconstructMeter check d FX FY FM FN)≤fee*
 (9*N+((8*(N+2)^2+2)*N+2)*N+7+(K+2*(2*N+2)+2)*(FM.length*FN.length)) :=
 Nat.mul_le_mul_left fee (reconstruct_work check d FX FY FM FN N K hx hy hFX hFY hFM hFN checker)
end Universal233.Rule5LocalWork
