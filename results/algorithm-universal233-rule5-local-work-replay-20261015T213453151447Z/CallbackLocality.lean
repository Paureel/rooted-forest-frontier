import CallDecrease
import PlanCover
import LocalExact
namespace Universal233.BothBadLocal
open RMAF CoreProgram ForestState RestrictionBridge VertexGeometry SourceCoverage
open BothBad
abbrev Ordinary := Tree → Tree → Nat → Option Forest
def BelowIH (q : Nat) (actual : Ordinary) : Prop := ∀r,r<q → ForestMinCompletion.LocalOrdinaryIH r actual

/-- Answer locality on ALL callback inputs; properness is not a premise. -/
theorem ordinaryExecution_answer_congr_at (f g : ForestSolver) (K : Nat)
 (equal : ∀T ss r,r≤K → f T ss r=g T ss r)
 (T S : Tree) (Q : Forest) (b : Nat) (low : b≤K) :
 (ordinaryExecution f T S Q b).answer=(ordinaryExecution g T S Q b).answer := by
 rw [ordinaryExecution_value,ordinaryExecution_value]
 unfold MafScheduler.solveDisjoint MafScheduler.attempt
 cases prep : MafScheduler.prepare T S Q with
 | none => rfl
 | some js =>
  have heq := GenericForest.LocalIH.schedule_congr
   (MafScheduler.recursive T S (asTree f)) (MafScheduler.recursive T S (asTree g)) b js
   (by
    intro U r hr
    cases rt : restrict U T with
    | none => simp [MafScheduler.recursive,rt]
    | some t =>
     cases rs : restrict U S with
     | none => simp [MafScheduler.recursive,rs]
     | some s =>
      simpa only [MafScheduler.recursive,rt,rs,asTree] using
       congrArg (Option.map (fun F : Forest=>(F.length-1,F))) (equal (some t) [s] r (Nat.le_trans hr low)))
  simp only [Option.map_some,Option.bind_some,heq]

theorem dispatch_answer_congr_at (f g : ForestSolver) (K : Nat)
 (equal : ∀T ss r,r≤K → f T ss r=g T ss r)
 (T S : Tree) (e : Entry) (low : e.budget≤K) :
 (dispatch f T S e).answer=(dispatch g T S e).answer := by
 cases e with
 | mk out mode b =>
  cases mode with
  | ordinary => exact ordinaryExecution_answer_congr_at f g K equal T S out.partition b low
  | full => exact equal _ _ b low
  | retained A B C known =>
   exact congrArg (Option.map (fun F : Forest=>known++F++[C])) (equal _ _ b low)

theorem execute_answer_congr_entries (f g : ForestSolver) (T S : Tree) (q : Nat) (xs : List Entry)
 (equal : ∀e,e∈xs → (dispatch f T S e).answer=(dispatch g T S e).answer) :
 (execute f T S q xs).answer=(execute g T S q xs).answer := by
 induction xs with
 | nil => rfl
 | cons e es ih =>
  have head := equal e (by simp)
  have tail := ih (fun e he=>equal e (by simp [he]))
  change choose (checked T S q (dispatch f T S e).answer) (execute f T S q es).answer =
   choose (checked T S q (dispatch g T S e).answer) (execute g T S q es).answer
  rw [head,tail]

/-- Literal planned entries, including entries never reached by a callback,
have the full original source cost charged before their budgets are formed. -/
theorem plan_entry_budget_drop (S T : Tree) (A B C : List Nat)
 (edge : RMAF.Vertex × RMAF.Vertex) (q : Nat) (e : Entry)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (hl : ∀x,x∈leaves S → x∈leaves T)
 (hp : partitionCheck (leaves S) [A,B,C]=true)
 (selected : PairGeometry.choose T A B=some (.edge edge))
 (mem : e∈plan S T A B C (PairGeometry.descendants T edge.2) q) : e.budget+3≤q := by
 have paid := plan_budget S T A B C (PairGeometry.descendants T edge.2) q e mem
 have source := plan_sources S T A B C edge hs ht hl hp selected q e mem
 have ranks := selected_ranks S T A B C edge ht hl hp selected
 have mincost : 3≤e.output.sourceCuts.length := by
  rcases List.mem_append.1 source with ha|hb
  · have h := generate_color_cost S (BinaryCheap.cheapColor A B (PairGeometry.descendants T edge.2)) q e.output ha
    change RankDichotomy.inputRank S (BinaryCheap.cheapColor A B (PairGeometry.descendants T edge.2))≤e.output.sourceCuts.length+1 at h
    rw [ranks.1] at h
    omega
  · have h := generate_color_cost S (BinaryCheap.cheapColor B A (PairGeometry.descendants T edge.2)) q e.output hb
    change RankDichotomy.inputRank S (BinaryCheap.cheapColor B A (PairGeometry.descendants T edge.2))≤e.output.sourceCuts.length+1 at h
    rw [ranks.2] at h
    omega
 omega
end Universal233.BothBadLocal
