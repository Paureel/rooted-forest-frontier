import MergeEnumeration
namespace Universal233.Rule5LocalWork
open RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller

def bestMeter (check : Forest→Measured Bool) : List Forest→Measured (Option Forest)
 | [] => ⟨none,1⟩
 | G::gs => let c:=check G;let r:=bestMeter check gs
            let v:=if c.value then
               match r.value with
               | none => some G
               | some H => if G.length-1≤H.length-1 then some G else some H
              else r.value
            /- Both cost lengths are conservatively paid even when the guard
            or recursive none result avoids them. -/
            ⟨v,c.work+r.work+G.length+(r.value.map List.length).getD 0+4⟩

theorem best_literal (check : Forest→Measured Bool) (gs : List Forest) :
 (bestMeter check gs).value=best (fun G=>G.length-1) (fun G=>(check G).value) gs := by
 induction gs with
 | nil => rfl
 | cons G gs ih =>
   simp only [bestMeter,best,ih]
   split <;> simp_all
   cases hs : best (fun G=>G.length-1) (fun G=>(check G).value) gs <;> simp_all

theorem best_value (T S : Tree) (check : Forest→Measured Bool) (gs : List Forest)
 (binding : ∀G,G∈gs →(check G).value=agreement T S G) :
 (bestMeter check gs).value=best (fun G=>G.length-1) (agreement T S) gs := by
 induction gs with
 | nil => rfl
 | cons G gs ih =>
   have tail := ih (fun H hh=>binding H (by simp [hh]))
   simp only [bestMeter,best,binding G (by simp),tail]
   split <;> simp_all
   cases hs : best (fun G=>G.length-1) (agreement T S) gs <;> simp_all

theorem best_work (check : Forest→Measured Bool) (gs : List Forest) (K L : Nat)
 (bill : ∀G,G∈gs →(check G).work≤K) (lengths : ∀G,G∈gs →G.length≤L) :
 (bestMeter check gs).work≤(K+2*(L+1)+2)*gs.length+1 := by
 induction gs with
 | nil => simp [bestMeter]
 | cons G gs ih =>
   have tail := ih (fun H hh=>bill H (by simp [hh])) (fun H hh=>lengths H (by simp [hh]))
   have head := bill G (by simp)
   have size := lengths G (by simp)
   have kept : ((bestMeter check gs).value.map List.length).getD 0≤L := by
     cases h : (bestMeter check gs).value with
     | none => simp
     | some H =>
       have literal : best (fun G=>G.length-1) (fun G=>(check G).value) gs=some H := by rw [←best_literal];exact h
       have mem := (best_spec _ _ gs H literal).1
       simpa using lengths H (by simp [mem])
   have step : (check G).work+G.length+((bestMeter check gs).value.map List.length).getD 0+4≤K+2*(L+1)+2 := by omega
   change (check G).work+(bestMeter check gs).work+G.length+((bestMeter check gs).value.map List.length).getD 0+4≤(K+2*(L+1)+2)*(gs.length+1)+1
   generalize K+2*(L+1)+2=C at tail step ⊢
   rw [Nat.mul_succ C gs.length]
   omega

theorem erase_flatten (H : List Nat) (F : Forest) : (F.erase H).flatten.length≤F.flatten.length := by
 induction F with
 | nil => simp
 | cons B F ih =>
   simp only [List.erase_cons]
   split <;> simp only [List.flatten_cons,List.length_append] <;> omega

theorem pair_payload (X Y : List Nat) (GM GN : Forest) (H J : List Nat) (N : Nat)
 (hM : cells GM≤N) (hN : cells GN≤N) (hH : H.length≤N) (hJ : J.length≤N) :
 cells (pairMeter X Y GM GN H J).value≤6*N+1 ∧
 (pairMeter X Y GM GN H J).value.length≤2*N+1 := by
 have hm : GM.length≤N ∧ GM.flatten.length≤N := by unfold cells at hM;omega
 have hn : GN.length≤N ∧ GN.flatten.length≤N := by unfold cells at hN;omega
 have fH := List.length_filter_le (X.contains ·) H
 have fJ := List.length_filter_le (Y.contains ·) J
 have em : (GM.erase H).length≤GM.length := List.length_erase_le
 have en : (GN.erase J).length≤GN.length := List.length_erase_le
 have emflat := erase_flatten H GM
 have enflat := erase_flatten J GN
 rw [pair_value]
 simp only [cells,merged,List.flatten_cons,List.flatten_append,List.length_cons,List.length_append]
 omega

/-- Every materialized checker input has this bound, including candidates
which fail agreement and duplicate candidates from different owner guesses. -/
theorem merge_payload (X Y : List Nat) (x y rho gamma : Nat) (FM FN : Forest) (N : Nat)
 (hM : cells FM≤N) (hN : cells FN≤N) {G : Forest}
 (mem : G∈(mergeMeter X Y x y rho gamma FM FN).value) : cells G≤6*N+1 ∧ G.length≤2*N+1 := by
 rw [merge_value] at mem
 unfold mergeCandidates at mem
 obtain ⟨H,hH,row⟩ := List.mem_flatMap.1 mem
 obtain ⟨J,hJ,eq⟩ := List.mem_map.1 row
 have hm : cells (relabelForest (swap y rho) FM)≤N := by rw [relabel_cells];exact hM
 have hn : cells (relabelForest (swap x gamma) FN)≤N := by rw [relabel_cells];exact hN
 have hhl := block_len _ H hH
 have hjl := block_len _ J hJ
 have bound := pair_payload X Y (relabelForest (swap y rho) FM) (relabelForest (swap x gamma) FN)
   H J N hm hn (by unfold cells at hm;omega) (by unfold cells at hn;omega)
 rw [pair_value] at bound
 simpa only [eq] using bound

def pickMeter (check : Forest→Measured Bool) (X Y : List Nat) (x y rho gamma : Nat)
 (FM FN : Forest) : Measured (Option Forest) :=
 let r:=mergeMeter X Y x y rho gamma FM FN
 let b:=bestMeter check r.value
 ⟨b.value,r.work+b.work⟩

theorem pick_value (T S : Tree) (check : Forest→Measured Bool) (X Y : List Nat)
 (x y rho gamma : Nat) (FM FN : Forest)
 (binding : ∀G,G∈mergeCandidates X Y x y rho gamma FM FN →(check G).value=agreement T S G) :
 (pickMeter check X Y x y rho gamma FM FN).value=pickMerge T S X Y x y rho gamma FM FN := by
 simp only [pickMeter,pickMerge]
 rw [merge_value]
 exact best_value T S check _ binding

/-- All unknown primitive work is confined to the actual agreement checker
on these bounded literal candidate payloads, not to a Rule5 LocalWorkBound. -/
theorem pick_work (check : Forest→Measured Bool) (X Y : List Nat) (x y rho gamma : Nat)
 (FM FN : Forest) (N K : Nat)
 (hX : X.length≤N) (hY : Y.length≤N) (hM : cells FM≤N) (hN : cells FN≤N)
 (checker : ∀G,G∈mergeCandidates X Y x y rho gamma FM FN →(check G).work≤K) :
 (pickMeter check X Y x y rho gamma FM FN).work≤
 4*N+((8*(N+2)^2+2)*N+2)*N+2+(K+2*(2*N+2)+2)*(FM.length*FN.length) := by
 have gen := merge_work X Y x y rho gamma FM FN N hX hY hM hN
 have lengths : ∀G,G∈(mergeMeter X Y x y rho gamma FM FN).value →G.length≤2*N+1 := by
   intro G hg;exact (merge_payload X Y x y rho gamma FM FN N hM hN hg).2
 have ck : ∀G,G∈(mergeMeter X Y x y rho gamma FM FN).value →(check G).work≤K := by
   rw [merge_value];exact checker
 have b := best_work check _ K (2*N+1) ck lengths
 rw [merge_occurrences] at b
 have coeff : K+2*(2*N+1+1)+2=K+2*(2*N+2)+2 := by omega
 rw [coeff] at b
 simp only [pickMeter]
 omega
end Universal233.Rule5LocalWork
