import ForestExecutionV3

namespace SourceForestV3
open RMAF ForestState GenericForest GenericForest.FrontierWork
open Universal233.PaidQueries SourceCouplingV2 SourceDisjointV2
open CallbackPairingAuthor (indexFrom)

variable {actual : GenericForest.FrontierWork.Ordinary}

theorem overlap_value_equation (hp : proper (some t) ss=true)
    (ha : agrees (some t) ss (ss.map leaves)=false) (hn : ss.length≠1)
    (ho : overlap t ss=some h) :
    GenericForest.solve actual (some t) ss q =
      best List.length (GenericForest.accepted (some t) ss q)
        (branchAnswers actual (some t) ss q (branches t ss h q)) := by
  cases ss with
  | nil =>
    simp only [List.map_nil] at ha
    simp [GenericForest.solve,hp,ha,ho,branchAnswers,eligible,cutCount]
    rfl
  | cons s rest =>
    cases rest with
    | nil => simp at hn
    | cons u rest =>
      simp only [List.map_cons] at ha
      simp [GenericForest.solve,hp,ha,ho,branchAnswers,eligible,cutCount]
      rfl

theorem overlap_debit_equation (hp : proper (some t) ss=true)
    (ha : agrees (some t) ss (ss.map leaves)=false) (hn : ss.length≠1)
    (ho : overlap t ss=some h) :
    OrdinaryDispatch.WorkRecursion.forestWork actual (fun _ _ _=>0) (some t) ss q =
      overlapLocal t ss h q+branchDebit actual (some t) ss q (branches t ss h q) := by
  cases ss with
  | nil =>
    simp only [List.map_nil] at ha
    simp [OrdinaryDispatch.WorkRecursion.forestWork,nonrecursiveBill,hp,ha,ho,
      overlapLocal,branchDebit,eligible,cutCount]
    rfl
  | cons s rest =>
    cases rest with
    | nil => simp at hn
    | cons u rest =>
      simp only [List.map_cons] at ha
      simp [OrdinaryDispatch.WorkRecursion.forestWork,nonrecursiveBill,hp,ha,ho,
        overlapLocal,branchDebit,eligible,cutCount]
      rfl

theorem overlap_frontier_equation (hp : proper (some t) ss=true)
    (ha : agrees (some t) ss (ss.map leaves)=false) (hn : ss.length≠1)
    (ho : overlap t ss=some h) :
    frontier actual (some t) ss q =
      branchQueries actual (some t) ss q (branches t ss h q) := by
  cases ss with
  | nil =>
    simp only [List.map_nil] at ha
    simp [frontier,hp,ha,ho,branchQueries,eligible,cutCount]
    rfl
  | cons s rest =>
    cases rest with
    | nil => simp at hn
    | cons u rest =>
      simp only [List.map_cons] at ha
      simp [frontier,hp,ha,ho,branchQueries,eligible,cutCount]
      rfl

theorem noJobs_corresponds (hp : proper (some t) ss=true)
    (ha : agrees (some t) ss (ss.map leaves)=false) (hn : ss.length≠1)
    (ho : overlap t ss=none) (hj : jobs t ss=none) :
    Corresponds actual k (some t) ss q ⟨none,inspectionBill (some t) ss q,[]⟩ := by
  cases ss with
  | nil =>
    simp only [List.map_nil] at ha
    simp [Corresponds,GenericForest.solve,disjointSolve,disjointAttempt,
      OrdinaryDispatch.WorkRecursion.forestWork,nonrecursiveBill,frontier,hp,ha,ho,hj,indexFrom]
  | cons s rest =>
    cases rest with
    | nil => simp at hn
    | cons u rest =>
      simp only [List.map_cons] at ha
      simp [Corresponds,GenericForest.solve,disjointSolve,disjointAttempt,
        OrdinaryDispatch.WorkRecursion.forestWork,nonrecursiveBill,frontier,hp,ha,ho,hj,indexFrom]

theorem disjointAt_corresponds
    (execution : ScheduleAt (PairChild OrdExec) mode q js k r slots)
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (hp : proper (some t) ss=true) (ha : agrees (some t) ss (ss.map leaves)=false)
    (hn : ss.length≠1) (ho : overlap t ss=none) (hj : jobs t ss=some js) :
    Corresponds (ordinarySpec mode base) k (some t) ss q
      ⟨r.value.answers.bind (fun xs=>checked (some t) ss q (xs.flatMap Prod.snd)),
        inspectionBill (some t) ss q+(r.callerWork+r.recursiveWork),slots⟩ := by
  have hr := scheduleAt_projection execution (fun p b a h=>pair_child_sound sound h)
  rw [mode_pair] at hr
  have hv := congrArg MeterReceipt.value hr
  rw [SourceCouplingV2.meterSchedule_value] at hv
  have hm : meterSchedule (pairCallback (ordinarySpec mode base)) (fun _ _=>0) q js =
      meterSchedule (fun p b=>(ordinarySpec mode base p.1 p.2 b).map
        (fun fs=>(fs.length-1,fs))) (fun _ _=>0) q js := rfl
  have hw := congrArg (fun m=>m.callerWork+m.recursiveWork) (hr.trans hm)
  have hi := scheduleAt_index execution
  cases ss with
  | nil =>
    simp only [List.map_nil] at ha
    refine ⟨?_,?_,?_⟩
    · simp [GenericForest.solve,hp,ha,ho,disjointSolve,disjointAttempt,hj,hv,pairCallback]
      rfl
    · simp [OrdinaryDispatch.WorkRecursion.forestWork,nonrecursiveBill,hp,ha,ho,hj]
      exact hw
    · simpa [frontier,hp,ha,ho,hj,hr] using hi
  | cons s rest =>
    cases rest with
    | nil => simp at hn
    | cons u rest =>
      simp only [List.map_cons] at ha
      refine ⟨?_,?_,?_⟩
      · simp [GenericForest.solve,hp,ha,ho,disjointSolve,disjointAttempt,hj,hv,pairCallback]
        rfl
      · simp [OrdinaryDispatch.WorkRecursion.forestWork,nonrecursiveBill,hp,ha,ho,hj]
        exact hw
      · simpa [frontier,hp,ha,ho,hj,hr] using hi

end SourceForestV3
