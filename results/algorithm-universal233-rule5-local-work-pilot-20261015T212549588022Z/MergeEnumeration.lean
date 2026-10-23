import MergeOperations
namespace Universal233.Rule5LocalWork
open RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller

def rowMeter (X Y : List Nat) (GM GN : Forest) (H : List Nat) : Forest→Measured (List Forest)
 | [] => ⟨[],1⟩
 | J::js => let p:=pairMeter X Y GM GN H J;let r:=rowMeter X Y GM GN H js
            ⟨p.value::r.value,p.work+r.work+1⟩

def ownersMeter (X Y : List Nat) (GM GN : Forest) : Forest→Measured (List Forest)
 | [] => ⟨[],1⟩
 | H::hs => let p:=rowMeter X Y GM GN H GN;let r:=ownersMeter X Y GM GN hs
            ⟨p.value++r.value,p.work+r.work+p.value.length+1⟩

theorem row_value (X Y : List Nat) (GM GN : Forest) (H : List Nat) (js : Forest) :
 (rowMeter X Y GM GN H js).value=js.map fun J=>
 merged (H.filter (X.contains ·)) (J.filter (Y.contains ·)) (GM.erase H) (GN.erase J) := by
 induction js with
 | nil => rfl
 | cons J js ih => simp only [rowMeter,List.map_cons,pair_value,ih]

theorem owners_value (X Y : List Nat) (GM GN hs : Forest) :
 (ownersMeter X Y GM GN hs).value=hs.flatMap fun H=>GN.map fun J=>
 merged (H.filter (X.contains ·)) (J.filter (Y.contains ·)) (GM.erase H) (GN.erase J) := by
 induction hs with
 | nil => rfl
 | cons H hs ih => simp only [ownersMeter,List.flatMap_cons,row_value,ih]

theorem row_work (X Y : List Nat) (GM GN : Forest) (H : List Nat) (js : Forest) (N : Nat)
 (hX : X.length≤N) (hY : Y.length≤N) (hM : cells GM≤N) (hN : cells GN≤N)
 (hH : H.length≤N) (hjs : ∀J,J∈js →J.length≤N) :
 (rowMeter X Y GM GN H js).work≤(8*(N+2)^2+1)*js.length+1 := by
 induction js with
 | nil => simp [rowMeter]
 | cons J js ih =>
   have pair := pair_work X Y GM GN H J N hX hY hM hN hH (hjs J (by simp))
   have tail := ih (fun K hk=>hjs K (by simp [hk]))
   simp only [rowMeter,List.length_cons,Nat.mul_add,Nat.mul_one]
   omega

theorem owners_work (X Y : List Nat) (GM GN hs : Forest) (N : Nat)
 (hX : X.length≤N) (hY : Y.length≤N) (hM : cells GM≤N) (hN : cells GN≤N)
 (hsbound : ∀H,H∈hs →H.length≤N) :
 (ownersMeter X Y GM GN hs).work≤((8*(N+2)^2+2)*GN.length+2)*hs.length+1 := by
 induction hs with
 | nil => simp [ownersMeter]
 | cons H hs ih =>
   have hn : GN.flatten.length≤N := by unfold cells at hN;omega
   have row := row_work X Y GM GN H GN N hX hY hM hN (hsbound H (by simp))
     (fun J hj=>Nat.le_trans (block_len GN J hj) hn)
   have tail := ih (fun K hk=>hsbound K (by simp [hk]))
   have len : (rowMeter X Y GM GN H GN).value.length=GN.length := by rw [row_value,List.length_map]
   simp only [ownersMeter,len,List.length_cons,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
   simp only [Nat.add_mul,Nat.one_mul] at row
   omega

/-- Relabel visits every original cell once and every block once; the scalar
swap fee (two Nat equality tests) is supplied separately. -/
def mergeMeter (X Y : List Nat) (x y rho gamma : Nat) (FM FN : Forest) : Measured (List Forest) :=
 let GM:=relabelForest (swap y rho) FM
 let GN:=relabelForest (swap x gamma) FN
 let r:=ownersMeter X Y GM GN GM
 ⟨r.value,2*cells FM+2*cells FN+r.work⟩

theorem merge_value (X Y : List Nat) (x y rho gamma : Nat) (FM FN : Forest) :
 (mergeMeter X Y x y rho gamma FM FN).value=mergeCandidates X Y x y rho gamma FM FN := by
 simp only [mergeMeter,owners_value,mergeCandidates]

theorem relabel_cells (f : Nat→Nat) (F : Forest) : cells (relabelForest f F)=cells F := by
 unfold cells
 have flat : (relabelForest f F).flatten=F.flatten.map f := List.map_flatten.symm
 rw [flat,List.length_map]
 simp [relabelForest]

/-- Polynomial in actual payload. Invalid and duplicate owner occurrences are
included; no successful-owner or chosen-minimum count is used. -/
theorem merge_work (X Y : List Nat) (x y rho gamma : Nat) (FM FN : Forest) (N : Nat)
 (hX : X.length≤N) (hY : Y.length≤N) (hM : cells FM≤N) (hN : cells FN≤N) :
 (mergeMeter X Y x y rho gamma FM FN).work≤
 4*N+((8*(N+2)^2+2)*N+2)*N+1 := by
 have hm := relabel_cells (swap y rho) FM
 have hn := relabel_cells (swap x gamma) FN
 have flen : FM.length≤N := by unfold cells at hM;omega
 have nlen : FN.length≤N := by unfold cells at hN;omega
 have bound := owners_work X Y (relabelForest (swap y rho) FM) (relabelForest (swap x gamma) FN)
   (relabelForest (swap y rho) FM) N hX hY (by omega) (by omega) ?_
 · have p1 := Nat.mul_le_mul_left (8*(N+2)^2+2) nlen
   have p2 := Nat.mul_le_mul (Nat.add_le_add_right p1 2) flen
   simp only [relabelForest,List.length_map] at bound
   simp only [mergeMeter]
   omega
 · intro H hh
   have sub := block_len _ H hh
   unfold cells at hm
   omega

theorem merge_occurrences (X Y : List Nat) (x y rho gamma : Nat) (FM FN : Forest) :
 (mergeMeter X Y x y rho gamma FM FN).value.length=FM.length*FN.length := by
 rw [merge_value,mergeCandidates_length]
end Universal233.Rule5LocalWork
