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
end Universal233.GroupedFullQuery
