import DisjointConsumerV2

namespace SourceChildrenV2
open RMAF Universal233 Universal233.CherryBranching
open Universal233.Rule5SelectedLocalWork

theorem children_tick_credit
    (h : ChildrenRun FExec T q cs r debits ticks) : ticks ≤ 8*r.localWork := by
  induction h with
  | nil => decide
  | cons head tail ih =>
    cases head with
    | refused over => simp only [prependChild,List.length_nil]; omega
    | returned paid execution => simp only [prependChild,List.length_cons,List.length_nil]; omega

theorem children_exists
    (total : ∀ t ss b, ∃ fr, FExec t ss b fr)
    (T : Tree) (q : Nat) (cs : List Child) :
    ∃ r debits ticks, ChildrenRun FExec T q cs r debits ticks := by
  induction cs with
  | nil => exact ⟨_,_,_,ChildrenRun.nil⟩
  | cons c cs ih =>
    obtain ⟨r,debits,ticks,hr⟩ := ih
    by_cases hp : c.paid≤q
    · obtain ⟨fr,hfr⟩ := total (some T) c.sourceForest (q-c.paid)
      exact ⟨_,_,_,ChildrenRun.cons (ChildRun.returned hp hfr) hr⟩
    · exact ⟨_,_,_,ChildrenRun.cons (ChildRun.refused hp) hr⟩

end SourceChildrenV2

namespace SourceDisjointV2
open RMAF ForestState GenericForest GenericForest.FrontierWork
open Universal233.PaidQueries SourceCouplingV2

theorem disjoint_scheduler_credit
    (h : Schedule (PairChild OrdExec) mode q js r slots ticks)
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (hj : jobs t ss = some js)
    (hp : proper (some t) ss = true)
    (ha : agrees (some t) ss (ss.map leaves) = false)
    (ho : overlap t ss = none) (hn : ss.length ≠ 1) :
    ticks ≤ 8*OrdinaryDispatch.WorkRecursion.forestWork (ordinarySpec mode base)
      (fun _ _ _=>0) (some t) ss q := by
  have ht := schedule_tick_credit h
  have hw := disjoint_work h sound hj hp ha ho hn
  omega

theorem forest_disjoint_value
    (h : Schedule (PairChild OrdExec) mode q js r slots ticks)
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (hj : jobs t ss = some js)
    (hp : proper (some t) ss = true)
    (ha : agrees (some t) ss (ss.map leaves) = false)
    (ho : overlap t ss = none) (hn : ss.length ≠ 1) :
    r.value.answers.bind (fun xs=>checked (some t) ss q (xs.flatMap Prod.snd)) =
      GenericForest.solve (ordinarySpec mode base) (some t) ss q := by
  have hv := disjoint_value h sound hj
  cases ss with
  | nil =>
    simp only [List.map_nil] at ha
    simpa [GenericForest.solve,hp,ha,ho] using hv
  | cons s rest =>
    cases rest with
    | nil => simp at hn
    | cons u rest =>
      simp only [List.map_cons] at ha
      simpa [GenericForest.solve,hp,ha,ho] using hv

end SourceDisjointV2
