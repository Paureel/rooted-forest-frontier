import DisjointTrace
namespace OrdinaryDispatch.Hard2Size
open RMAF ForestState ForestGroups RestrictionBridge Universal233 Universal233.BothBad

def TargetBound (T : Tree) (target : Option Tree) : Prop :=
 (∀x,x∈labels target→x∈leaves T) ∧ (labels target).length≤(leaves T).length

theorem self_target_bound (T : Tree) : TargetBound T (some T) := ⟨fun _ hx=>hx,Nat.le_refl _⟩

theorem local_target_bound (T : Tree) (U : List Nat) : TargetBound T (localTarget (some T) U) := by
 have eq : labels (localTarget (some T) U)=(leaves T).filter (U.contains ·) := by
  change optionLeaves (restrict U T)=(leaves T).filter (U.contains ·)
  exact restrict_leaves T U
 rw [TargetBound,eq]
 exact ⟨fun _ hx=>(List.mem_filter.1 hx).1,List.length_filter_le _ _⟩

theorem restricted_target_bound (T t : Tree) (U : List Nat) (hr : restrict U T=some t) : TargetBound T (some t) := by
 simpa only [localTarget,Option.bind_some,hr] using local_target_bound T U

theorem ordinary_execution_target_bound (solve : ForestSolver) (T S : Tree) (Q : List (List Nat))
 (b : Nat) (call : Call) (mem : call∈(ordinaryExecution solve T S Q b).calls) : TargetBound T call.target := by
 cases hp : MafScheduler.prepare T S Q with
 | none => simp [ordinaryExecution,hp] at mem
 | some js =>
  simp only [ordinaryExecution,hp] at mem
  obtain ⟨ub,hub,hmap⟩ := List.mem_filterMap.1 mem
  cases ht : restrict ub.1 T <;> cases hs : restrict ub.1 S <;> simp only [ht,hs] at hmap
  all_goals first | contradiction | (have eq := Option.some.inj hmap;subst call;exact restricted_target_bound T _ ub.1 ht)

theorem dispatch_target_bound (solve : ForestSolver) (T S : Tree) (e : BothBad.Entry)
 (call : Call) (mem : call∈(dispatch solve T S e).calls) : TargetBound T call.target := by
 cases e with
 | mk o mode b =>
  cases mode with
  | ordinary => exact ordinary_execution_target_bound solve T S _ b call mem
  | full =>
   have eq : call=⟨some T,OutputState.sourceForest S o.partition,b⟩ := by simpa [dispatch] using mem
   subst call;exact self_target_bound T
  | retained a residual completed known =>
   have eq : call=⟨localTarget (some T) residual,owned (OutputState.sourceForest S o.partition) residual,b⟩ := by simpa [dispatch] using mem
   subst call;exact local_target_bound T residual

theorem execute_target_bound (solve : ForestSolver) (T S : Tree) (q : Nat) (xs : List BothBad.Entry)
 (call : Call) (mem : call∈(execute solve T S q xs).calls) : TargetBound T call.target := by
 rw [execute_calls] at mem
 obtain ⟨e,he,hcall⟩ := List.mem_flatMap.1 mem
 exact dispatch_target_bound solve T S e call hcall
end OrdinaryDispatch.Hard2Size
