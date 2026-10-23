import FullStateSchedule
import QueryWork
namespace Universal233.GroupedFullQuery
open RMAF ForestState ForestGroups RestrictionBridge PaidQueries

theorem answers_reconstruct (T : Option Tree) (ss : List Tree)
 {js : List (Job Problem Forest)} {xs : List (Nat × Forest)} (a : Answers js xs)
 (Q : Forest) (eq : js.map Job.problem=groupProblems T ss Q) (nd : Q.Nodup) :
 ∃ G : List Nat → Forest,
   (∀ U∈Q,agrees (localTarget T U) (owned ss U) (G U)=true) ∧
   Q.flatMap G=xs.flatMap Prod.snd ∧
   (Q.map (fun U => additionalCost (owned ss U) (G U))).sum=answerCost xs := by
 induction a generalizing Q with
 | nil =>
   have hQ : Q=[] := by cases Q <;> simp_all [groupProblems]
   subst Q
   exact ⟨fun _ => [],by simp,by simp,by simp [answerCost]⟩
 | @cons j x js xs hx ha ih =>
   cases Q with
   | nil => simp [groupProblems] at eq
   | cons U Q =>
     have he : j.problem=groupProblem T ss U ∧ js.map Job.problem=groupProblems T ss Q := by
       simpa [groupProblems] using eq
     have hn := List.nodup_cons.1 nd
     obtain ⟨H,hH,flat,bal⟩ := ih Q he.2 hn.2
     let G : List Nat → Forest := fun V => if V=U then x.2 else H V
     have tail : ∀ V∈Q,G V=H V := by
       intro V hV
       have ne : V≠U := by intro h;subst V;exact hn.1 hV
       simp [G,ne]
     have flatTail : Q.flatMap G=Q.flatMap H := List.flatMap_congr_left tail
     have costTail : (Q.map (fun V => additionalCost (owned ss V) (G V))).sum=
       (Q.map (fun V => additionalCost (owned ss V) (H V))).sum := by
       congr 1
       exact List.map_congr_left (fun V hV => congrArg (additionalCost (owned ss V)) (tail V hV))
     refine ⟨G,?_,?_,?_⟩
     · intro V hV
       rcases List.mem_cons.1 hV with rfl|hV
       · simpa [valid,he.1,groupProblem,G] using hx.1
       · rw [tail V hV];exact hH V hV
     · simpa [List.flatMap_cons,G,flatTail,flat] using rfl
     · have head : additionalCost (owned ss U) x.2=x.1 := by
         simpa [cost,he.1,groupProblem] using hx.2.1.symm
       simp only [List.map_cons,List.sum_cons,answerCost,List.map_cons,List.sum_cons] at *
       simpa [G,costTail,bal,head]

theorem potential_problems (H : Problem → Forest) (js : List (Job Problem Forest)) :
 potential H js=((js.map Job.problem).map (fun p => cost p (H p))).sum := by
 induction js <;> simp_all [potential]

def witnessFor (F : Forest) (p : Problem) : Forest := family p.key F

theorem original_witness (T : Option Tree) (ss : List Tree) (Q F : Forest)
 (js : List (Job Problem Forest)) (prep : prepare (groupProblems T ss Q)=some js)
 (ha : agrees T ss F=true) (hq : partitionCheck (labels T) Q=true) (own : Owns ss Q) :
 Supports (witnessFor F) js ∧ potential (witnessFor F) js=additionalCost ss F := by
 have he := (prepare_spec _ _ prep).1
 refine ⟨?_,?_⟩
 · intro j hj
   have hm : j.problem∈groupProblems T ss Q := by rw [←he];exact List.mem_map.2 ⟨j,hj,rfl⟩
   obtain ⟨U,hU,eq⟩ := List.mem_map.1 hm
   rw [←eq]
   exact local_forward T ss Q F ha hq own U hU
 · rw [potential_problems,he]
   simpa [groupProblems,groupProblem,witnessFor,cost,List.map_map,Function.comp_def] using
     forward_exact_cost T ss Q F ha hq own

/-- The returned whole-state answer is reconstructed from literal current
source groups, even when sources overlap in the target inside one group. -/
theorem grouped_sound (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (T : Option Tree) (ss : List Tree) (Q : Forest) (js : List (Job Problem Forest))
 (prep : prepare (groupProblems T ss Q)=some js) (bad : 2≤badSlots js)
 (hp : proper T ss=true) (hq : partitionCheck (labels T) Q=true)
 (own : Owns ss Q) (cross : CrossClear T ss Q)
 (xs : List (Nat × Forest)) (result : (schedule (callback actual) q js).answers=some xs) :
 let F := xs.flatMap Prod.snd
 agrees T ss F=true ∧ additionalCost ss F=answerCost xs ∧ additionalCost ss F≤q ∧
   ∀ H,agrees T ss H=true → F.length≤H.length := by
 obtain ⟨ax,budget⟩ := schedule_sound_at actual q below js bad (prepare_spec _ _ prep).2 xs result
 obtain ⟨G,hG,flat,bal⟩ := answers_reconstruct T ss ax Q (prepare_spec _ _ prep).1
   (checked_family_nodup _ _ hq)
 have valid := reverse_reconstruction T ss Q G hp hq own cross hG
 have costs := reverse_exact_cost T ss Q G hp hq own hG
 rw [flat] at valid costs
 have bill : additionalCost ss (xs.flatMap Prod.snd)=answerCost xs := by omega
 refine ⟨valid,bill,by omega,?_⟩
 intro H hH
 obtain ⟨support,pot⟩ := original_witness T ss Q H js prep hH hq own
 have least := answers_le (witnessFor H) ax support
 rw [pot,←bill] at least
 have h1 := sources_le_blocks T ss (xs.flatMap Prod.snd) valid
 have h2 := sources_le_blocks T ss H hH
 simp only [additionalCost] at least
 omega

theorem grouped_complete (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (T : Option Tree) (ss : List Tree) (Q : Forest) (js : List (Job Problem Forest))
 (prep : prepare (groupProblems T ss Q)=some js) (bad : 2≤badSlots js)
 (hq : partitionCheck (labels T) Q=true) (own : Owns ss Q)
 (F : Forest) (ha : agrees T ss F=true) (budget : additionalCost ss F≤q) :
 ∃ xs,(schedule (callback actual) q js).answers=some xs ∧
   answerCost xs≤additionalCost ss F := by
 obtain ⟨support,pot⟩ := original_witness T ss Q F js prep ha hq own
 obtain ⟨xs,result,_,best⟩ := schedule_complete_at actual q below js bad (prepare_spec _ _ prep).2
   (witnessFor F) support (by omega)
 exact ⟨xs,result,by omega⟩

/-- None means preparation refusal; some receipt with answers=none means
bounded infeasibility. All original source trees stay in their literal jobs. -/
def execute (actual : Ordinary) (T : Option Tree) (ss : List Tree) (Q : Forest) (q : Nat) :
 Option (Receipt Forest) := (prepare (groupProblems T ss Q)).map (schedule (callback actual) q)

def fullTrace (actual : Ordinary) (q : Nat) (js : List (Job Problem Forest)) : List (Problem × Nat) :=
 (meterSchedule (callback actual) (fun _ _ => 0) q js).queries

theorem fullTrace_budgets (actual : Ordinary) (q : Nat) (js : List (Job Problem Forest)) :
 (fullTrace actual q js).map Prod.snd=(schedule (callback actual) q js).calls :=
 (meterSchedule_trace (callback actual) (fun _ _ => 0) q js).1

theorem fullTrace_mass (actual : Ordinary) (q : Nat) (js : List (Job Problem Forest))
 (bad : 2≤badSlots js) (c : Rat) (hc : 2≤c) :
 actualQueryMass c q ((fullTrace actual q js).map Prod.snd)≤c^(-1 : Int) := by
 rw [fullTrace_budgets]
 exact actual_mass actual q js bad c hc

theorem fullTrace_strict (actual : Ordinary) (q : Nat) (js : List (Job Problem Forest))
 (bad : 2≤badSlots js) (p : Problem) (r : Nat) (hr : (p,r)∈fullTrace actual q js) : r<q := by
 apply actual_query_strict actual q js bad r
 rw [←fullTrace_budgets]
 exact List.mem_map.2 ⟨(p,r),hr,rfl⟩
end Universal233.GroupedFullQuery
