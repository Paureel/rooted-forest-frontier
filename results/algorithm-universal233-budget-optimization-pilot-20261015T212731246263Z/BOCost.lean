import BOOptimize
namespace OrdinaryDispatch.BudgetOptimization
open RMAF Universal233

/-- Additive charge of every actual external decision call, failed or successful.
queryWork is an explicit consumer-supplied cost, not a proved FastOrdinary cost. -/
def trialWork (queryWork : Nat → Nat) (trials : List Trial) : Nat :=
 (trials.map (fun t => queryWork t.1)).sum

def consecutiveWork (queryWork : Nat → Nat) (start : Nat) : Nat → Nat
 | 0 => 0
 | n+1 => queryWork start + consecutiveWork queryWork (start+1) n

theorem failed_work (w : Nat→Nat) (start n : Nat) :
 trialWork w (failedTrials start n)=consecutiveWork w start n := by
 induction n generalizing start with
 | zero => rfl
 | succ n ih => simp [trialWork,failedTrials,consecutiveWork] at *;exact ih _

theorem consecutive_snoc (w : Nat→Nat) (start n : Nat) :
 consecutiveWork w start (n+1)=consecutiveWork w start n+w (start+n) := by
 induction n generalizing start with
 | zero => simp [consecutiveWork]
 | succ n ih =>
   simp only [consecutiveWork,ih]
   have eq : start+1+n=start+(n+1) := by omega
   rw [eq]
   omega

theorem actual_trial_work (T S : Tree) (hp : DepthOne.proper T S=true) (w : Nat→Nat) :
 ∃q F,(optimize T S).search.selected=some (q,F) ∧
 trialWork w (optimize T S).search.trials=consecutiveWork w 0 (q+1) := by
 obtain ⟨q,F,o,sel,tr,rest⟩ := optimization_exact T S hp
 refine ⟨q,F,sel,?_⟩
 simp only [tr,trialWork,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
 change trialWork w (failedTrials 0 q)+w q=consecutiveWork w 0 (q+1)
 rw [failed_work,consecutive_snoc]
 simp

theorem consecutive_bound (w : Nat→Nat) (start fuel : Nat) (B : Rat)
 (h : ∀b,start≤b → b<start+fuel → (w b:Rat)≤B) :
 (consecutiveWork w start fuel:Rat)≤(fuel:Rat)*B := by
 induction fuel generalizing start with
 | zero => simp [consecutiveWork]
 | succ fuel ih =>
   have hd := h start (by omega) (by omega)
   have ht := ih (start+1) (fun b hb he => h b (by omega) (by omega))
   have sum := Rat.add_le_add hd ht
   simpa [consecutiveWork,Rat.natCast_add,Rat.add_mul,Rat.one_mul,Rat.add_comm] using sum

/-- c>1 suffices for all decision trials, without discarding failures. P is a
nonnegative monotone coefficient; a polynomial P gives a polynomial result. -/
theorem decision_sum_bound (w : Nat→Nat) (P : Nat→Rat) (q : Nat) (c : Rat)
 (hc : 1<c) (hP : 0≤P q) (mono : ∀b,b≤q → P b≤P q)
 (perQuery : ∀b,b≤q → (w b:Rat)≤P b*c^b) :
 (consecutiveWork w 0 (q+1):Rat)≤((q+1:Nat):Rat)*P q*c^q := by
 have hc0 : 0≤c := by grind
 have all : ∀b,0≤b → b<0+(q+1) → (w b:Rat)≤P q*c^q := by
   intro b _ hb
   have le : b≤q := by omega
   have first := Rat.mul_le_mul_of_nonneg_right (mono b le) (Rat.pow_nonneg (n:=b) hc0)
   have second := Rat.mul_le_mul_of_nonneg_left (SourceCoverage.qpow_mono c (by grind) le) hP
   exact Rat.le_trans (perQuery b le) (Rat.le_trans first second)
 have bound := consecutive_bound w 0 (q+1) (P q*c^q) all
 simpa [Rat.mul_assoc] using bound

/-- Printed primitive-cost interface: preflight pays properness, leaf count and
encoding; perTrial pays the local let/match, successor and retained cons cell;
finishCharge pays final selection/record construction. It excludes query and
recovery work, which are added separately exactly at their actual call sites. -/
def wrapperCharge (preflight perTrial finishCharge : Nat) (r : Execution) : Nat :=
 preflight+perTrial*r.search.trials.length+finishCharge

def totalCharge (w : Nat→Nat) (preflight perTrial finishCharge : Nat) (S : Tree) (r : Execution) : Nat :=
 trialWork w r.search.trials+wrapperCharge preflight perTrial finishCharge r+
 (r.recoveries.map (fun call => (FinalCutRecovery.meterRecover S call.1).work)).sum

/-- Exact additive accounting: all failed trials plus the successful trial,
linear wrapper operations, and precisely the one final recovery. -/
theorem total_charge_exact (T S : Tree) (hp : DepthOne.proper T S=true)
 (w : Nat→Nat) (preflight perTrial finishCharge : Nat) :
 ∃q F o,(optimize T S).search.selected=some (q,F) ∧
 (optimize T S).output=some o ∧ agreement T S F=true ∧ F.length=q+1 ∧
 totalCharge w preflight perTrial finishCharge S (optimize T S)=
 consecutiveWork w 0 (q+1)+
 (preflight+perTrial*(q+1)+finishCharge)+(FinalCutRecovery.meterRecover S F).work := by
 obtain ⟨q,F,o,sel,tr,out,rec,yes,recovered,af,oaf,rest⟩ := optimization_exact T S hp
 have len := (selected_minimum T S hp q F (by simpa [optimize,hp,finish] using sel)).2.1
 refine ⟨q,F,o,sel,out,af,len,?_⟩
 have tw : trialWork w (optimize T S).search.trials=consecutiveWork w 0 (q+1) := by
   simp only [tr,trialWork,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
   change trialWork w (failedTrials 0 q)+w q=consecutiveWork w 0 (q+1)
   rw [failed_work,consecutive_snoc];simp
 simp [totalCharge,wrapperCharge,tw,tr,rec,failed_length]

/-- The final coefficient contains no unknown forest sizes: checked flatten and
block bounds replace them by the original source leaf count. -/
def recoveryPolynomial (S : Tree) : Nat :=
 let n := (leaves S).length
 let m := CoreWork.treeNodes S
 (4096*(m+n+n+2)^8+32*n*(n+n+1)+CoreWork.initialCharge S+1)+
   2*(CoreWork.cap (CoreWork.inputResource S)+6)*n

theorem finalPolynomial_uniform (S : Tree) (F : CommonForest)
 (hn : (leaves S).Nodup) (hp : partitionCheck (leaves S) F=true) :
 FinalCutRecovery.finalPolynomial S F≤recoveryPolynomial S := by
 have flat := (FinalCutRecovery.checked_flatten_perm S F hn hp).length_eq
 have blocks := FinalCutRecovery.blocks_le_flatten F (SourceCoverage.partitionCheck_nonempty _ _ hp)
 have flen : F.length≤(leaves S).length := by omega
 have base : CoreWork.treeNodes S+F.flatten.length+F.length+2≤
   CoreWork.treeNodes S+(leaves S).length+(leaves S).length+2 := by omega
 have guard := Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left base 8)
 have color := Nat.mul_le_mul_left (32*(leaves S).length)
   (show F.flatten.length+F.length+1≤(leaves S).length+(leaves S).length+1 by omega)
 have core := Nat.mul_le_mul_left (2*(CoreWork.cap (CoreWork.inputResource S)+6)) flen
 unfold FinalCutRecovery.finalPolynomial FinalCutRecovery.guardCharge FinalCutRecovery.colorCharge recoveryPolynomial
 omega

/-- General conditional conversion. The recovery premise is explicit for c>1;
the licensed completed recovery theorem discharges it for c>=2 below. -/
theorem all_work_bound (w : Nat→Nat) (P : Nat→Rat) (q : Nat) (c : Rat)
 (wrapper final : Nat) (recovery : Nat) (hc : 1<c)
 (hP : 0≤P q) (mono : ∀b,b≤q → P b≤P q)
 (perQuery : ∀b,b≤q → (w b:Rat)≤P b*c^b)
 (finalBound : (recovery:Rat)≤(final:Rat)*c^q) :
 ((consecutiveWork w 0 (q+1)+wrapper+recovery:Nat):Rat)≤
   (((q+1:Nat):Rat)*P q+(wrapper:Rat)+(final:Rat))*c^q := by
 have trial := decision_sum_bound w P q c hc hP mono perQuery
 have power : 1≤c^q := by
   have h := SourceCoverage.qpow_mono c (by grind) (Nat.zero_le q)
   simpa using h
 have wrap := Rat.mul_le_mul_of_nonneg_left power (show 0≤(wrapper:Rat) from Rat.natCast_le_natCast.2 (Nat.zero_le _))
 simp only [Rat.mul_one] at wrap
 have total := Rat.add_le_add (Rat.add_le_add trial wrap) finalBound
 simpa [Rat.natCast_add,Rat.add_mul] using total

end OrdinaryDispatch.BudgetOptimization
