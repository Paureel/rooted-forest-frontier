import BadGroups
namespace Universal233.GroupedFullQuery
open RMAF ForestState ForestGroups RestrictionBridge PaidQueries

theorem execute_nonrefusal (actual : Ordinary) (T : Option Tree) (ss : List Tree) (Q : Forest) (q : Nat)
 (hp : proper T ss=true) (hq : partitionCheck (labels T) Q=true) (own : Owns ss Q) :
 ∃ r,execute actual T ss Q q=some r := by
 obtain ⟨js,prep⟩ := prepare_groups_exists T ss Q hp hq own
 exact ⟨schedule (callback actual) q js,by simp [execute,prep]⟩

theorem grouped_feasible_iff (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (T : Option Tree) (ss : List Tree) (Q : Forest) (js : List (Job Problem Forest))
 (prep : prepare (groupProblems T ss Q)=some js) (bad : 2≤badSlots js)
 (hp : proper T ss=true) (hq : partitionCheck (labels T) Q=true)
 (own : Owns ss Q) (cross : CrossClear T ss Q) :
 (∃ xs,(schedule (callback actual) q js).answers=some xs) ↔
 ∃ F,agrees T ss F=true ∧ additionalCost ss F≤q := by
 constructor
 · rintro ⟨xs,result⟩
   have h := grouped_sound actual q below T ss Q js prep bad hp hq own cross xs result
   exact ⟨xs.flatMap Prod.snd,h.1,h.2.2.1⟩
 · rintro ⟨F,ha,budget⟩
   obtain ⟨xs,result,_⟩ := grouped_complete actual q below T ss Q js prep bad hq own F ha budget
   exact ⟨xs,result⟩

theorem outer_mass_le (c : Rat) (hc : 2≤c) (b q : Nat) (bq : b≤q) (calls : List Nat) :
 actualQueryMass c q calls≤actualQueryMass c b calls := by
 induction calls with
 | nil => simp [actualQueryMass]
 | cons r rs ih =>
   have h := negpow_antitone c hc (b-r) (q-r) (Nat.sub_le_sub_right bq r)
   simp only [actualQueryMass,List.map_cons,List.sum_cons] at *
   grind

theorem actual_outer_mass (actual : Ordinary) (parentq b : Nat) (bq : b≤parentq)
 (js : List (Job Problem Forest)) (bad : 2≤badSlots js) (c : Rat) (hc : 2≤c) :
 actualQueryMass c parentq ((fullTrace actual b js).map Prod.snd)≤c^(-1 : Int) :=
 Rat.le_trans (outer_mass_le c hc b parentq bq _) (fullTrace_mass actual b js bad c hc)

theorem original_kept_bad_mass (actual : Ordinary) (parentq b : Nat) (bq : b≤parentq)
 (T S : Tree) (P : Forest) (A B C : List Nat)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hP : partitionCheck (leaves S) P=true) (hp : partitionCheck (leaves S) [A,B,C]=true)
 (keptA : A∈P) (keptC : C∈P)
 (badA : restrictionAgrees T S A=false) (badC : restrictionAgrees T S C=false)
 (js : List (Job Problem Forest))
 (prep : prepare (groupProblems (some T) (OutputState.sourceForest S P) [A++B,C])=some js)
 (c : Rat) (hc : 2≤c) :
 actualQueryMass c parentq ((fullTrace actual b js).map Prod.snd)≤c^(-1 : Int) := by
 have bad := kept_AB_C_badSlots T S P A B C hs ht same hP hp keptA keptC badA badC js prep
 exact actual_outer_mass actual parentq b bq js bad c hc

theorem meterRun_real_jobs (actual : Ordinary) (b : Nat) (js : List (Job Problem Forest))
 (p : Problem) (r : Nat) (hr : (p,r)∈(meterRun (callback actual) (fun _ _ => 0) b js).queries) :
 Job.hard p∈js ∧ r=b := by
 induction js with
 | nil => simp [meterRun] at hr
 | cons j js ih =>
   cases j with
   | resolved u c F =>
     obtain ⟨mem,eq⟩ := ih hr
     exact ⟨by simp [mem],eq⟩
   | hard u =>
     cases h : callback actual u b with
     | none =>
       have eq : (p,r)=(u,b) := by simpa [meterRun,h] using hr
       cases eq
       exact ⟨by simp,rfl⟩
     | some x =>
       simp only [meterRun,h] at hr
       rcases List.mem_cons.1 hr with eq|mem
       · cases eq;exact ⟨by simp,rfl⟩
       · obtain ⟨hm,eq⟩ := ih mem
         exact ⟨by simp [hm],eq⟩

theorem fullTrace_jobs (actual : Ordinary) (q : Nat) (js : List (Job Problem Forest))
 (p : Problem) (r : Nat) (hr : (p,r)∈fullTrace actual q js) : Job.hard p∈js := by
 unfold fullTrace meterSchedule at hr
 split at hr
 · simp at hr
 · exact (meterRun_real_jobs actual _ js p r hr).1

/-- Each recorded query is the literal restricted target and WHOLE owned source
list of an original group, with its actual strictly smaller residual. -/
theorem fullTrace_actual_group (actual : Ordinary) (q : Nat)
 (T : Option Tree) (ss : List Tree) (Q : Forest) (js : List (Job Problem Forest))
 (prep : prepare (groupProblems T ss Q)=some js) (bad : 2≤badSlots js)
 (p : Problem) (r : Nat) (hr : (p,r)∈fullTrace actual q js) :
 ∃ U∈Q,p.key=U ∧ p.target=localTarget T U ∧ p.sources=owned ss U ∧ r<q := by
 have hm := fullTrace_jobs actual q js p r hr
 have he := (prepare_spec _ _ prep).1
 have mem : p∈groupProblems T ss Q := by
   rw [←he]
   exact List.mem_map.2 ⟨Job.hard p,hm,rfl⟩
 obtain ⟨U,hU,eq⟩ := List.mem_map.1 mem
 exact ⟨U,hU,by rw [←eq];rfl,by rw [←eq];rfl,by rw [←eq];rfl,
   fullTrace_strict actual q js bad p r hr⟩

theorem prepare_malformed_refuses (ps : List Problem) (p : Problem) (mem : p∈ps)
 (malformed : proper p.target p.sources=false) : prepare ps=none := by
 cases h : prepare ps with
 | none => rfl
 | some js =>
   obtain ⟨eq,plans⟩ := prepare_spec ps js h
   have hp : p∈js.map Job.problem := by rw [eq];exact mem
   obtain ⟨j,hj,jp⟩ := List.mem_map.1 hp
   have plan := plans j hj
   have properP : proper p.target p.sources=true := by
     rw [←jp]
     cases j with
     | hard u => exact plan.1
     | resolved u c F => exact (agrees_parts _ _ _ plan.1).1
   simp [properP] at malformed
end Universal233.GroupedFullQuery
