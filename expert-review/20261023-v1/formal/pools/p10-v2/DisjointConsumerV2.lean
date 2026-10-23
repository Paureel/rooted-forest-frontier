import LocalCreditV2

namespace SourceDisjointV2
open RMAF ForestState GenericForest GenericForest.FrontierWork
open Universal233.PaidQueries SourceCouplingV2

abbrev F := List (List Nat)

def ordinarySpec (mode : Mode) (base : Tree → Tree → Nat → Option F)
    (T S : Tree) (b : Nat) : Option F :=
  if enabled mode b then base T S b else none

inductive PairChild (OrdExec : Tree → Tree → Nat → Option F → Prop) :
    (Tree × Tree) → Nat → Option (Nat × F) → Prop
  | returned (execution : OrdExec p.1 p.2 b a) :
      PairChild OrdExec p b (a.map (fun fs=>(fs.length-1,fs)))

theorem pair_child_sound
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (h : PairChild OrdExec p b a) : a=pairCallback base p b := by
  cases h with
  | returned execution => simp only [pairCallback,←sound _ _ _ _ execution]

theorem mode_pair (mode : Mode) (base : Tree → Tree → Nat → Option F) :
    specCallback mode (pairCallback base) = pairCallback (ordinarySpec mode base) := by
  funext p b
  cases he : enabled mode b <;> simp [specCallback,pairCallback,ordinarySpec,he]

theorem schedule_source
    (h : Schedule (PairChild OrdExec) mode q js r slots ticks)
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b) :
    r = meterSchedule (pairCallback (ordinarySpec mode base)) (fun _ _=>0) q js := by
  have hr := schedule_projection h (fun p b a h => pair_child_sound sound h)
  rw [mode_pair] at hr
  exact hr

theorem disjoint_value
    (h : Schedule (PairChild OrdExec) mode q js r slots ticks)
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (hj : jobs t ss = some js) :
    r.value.answers.bind (fun xs => checked (some t) ss q (xs.flatMap Prod.snd)) =
      disjointSolve t ss (ordinarySpec mode base) q := by
  have hr := schedule_source h sound
  have hv := congrArg MeterReceipt.value hr
  rw [SourceCouplingV2.meterSchedule_value] at hv
  simp only [disjointSolve,disjointAttempt,hj,Option.map_some,Option.bind_some]
  rw [hv]
  rfl

theorem disjoint_work
    (h : Schedule (PairChild OrdExec) mode q js r slots ticks)
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (hj : jobs t ss = some js)
    (hp : proper (some t) ss = true)
    (ha : agrees (some t) ss (ss.map leaves) = false)
    (ho : overlap t ss = none) (hn : ss.length ≠ 1) :
    inspectionBill (some t) ss q + (r.callerWork+r.recursiveWork) =
      OrdinaryDispatch.WorkRecursion.forestWork (ordinarySpec mode base)
        (fun _ _ _=>0) (some t) ss q := by
  have hr := schedule_source h sound
  have hm : meterSchedule (pairCallback (ordinarySpec mode base)) (fun _ _=>0) q js =
      meterSchedule (fun p b => (ordinarySpec mode base p.1 p.2 b).map
        (fun fs=>(fs.length-1,fs))) (fun _ _=>0) q js := rfl
  have hw := congrArg (fun m=>m.callerWork+m.recursiveWork) (hr.trans hm)
  cases ss with
  | nil =>
    simp only [List.map_nil] at ha
    simp [OrdinaryDispatch.WorkRecursion.forestWork,nonrecursiveBill,hp,ha,ho,hj]
    exact hw
  | cons s rest =>
    cases rest with
    | nil => simp at hn
    | cons u rest =>
      simp only [List.map_cons] at ha
      simp [OrdinaryDispatch.WorkRecursion.forestWork,nonrecursiveBill,hp,ha,ho,hj]
      exact hw

theorem disjoint_slot_index
    (h : Schedule (PairChild OrdExec) mode q js r slots ticks)
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (hj : jobs t ss = some js)
    (hp : proper (some t) ss = true)
    (ha : agrees (some t) ss (ss.map leaves) = false)
    (ho : overlap t ss = none) (hn : ss.length ≠ 1) :
    slots.map (fun s=>(s.index,s.query)) =
      CallbackPairingAuthor.indexFrom 0 (frontier (ordinarySpec mode base) (some t) ss q) := by
  have hr := schedule_source h sound
  have hi := schedule_slot_index h
  cases ss with
  | nil =>
    simp only [List.map_nil] at ha
    simpa [frontier,hp,ha,ho,hj,hr] using hi
  | cons s rest =>
    cases rest with
    | nil => simp at hn
    | cons u rest =>
      simp only [List.map_cons] at ha
      simpa [frontier,hp,ha,ho,hj,hr] using hi

end SourceDisjointV2
