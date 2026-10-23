import NumericLocal
namespace OrdinaryDispatch.GlobalNumeric
open RMAF ForestState Universal233 Universal233.CherryBranching
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open CoreGraph Integration VertexGeometry CutRealization HardParent
open Rule5Local Rule5Classification Rule5FinalClassification Rule5SourceOrientation Rule5OrdinaryDispatch
open Rule5ActualTrace

theorem common_direct_cap (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (a b : Nat) (d : BadSelection) (q M : Nat) (cap : PairCap M T S)
 {p : Tree×Tree} {r : Nat} (mem : (p,r)∈directQueries (commonTrace actual T S a b d q).calls) :
 PairCap (M+2) p.1 p.2 := by
 obtain ⟨j,hj,eq⟩:=List.mem_map.1 mem
 have job : j∈Rule5CommonSelector.commonJobs T S a b d q := by rw [←common_calls actual];exact hj
 unfold Rule5CommonSelector.commonJobs OrdinaryCommonSplit.Source.sourceJobs at job
 cases build : OrdinaryCommonSplit.Source.buildSetup T S (subtreeLabels S d.badArc)
     (Rule5CommonSelector.outsideLabels S a b d) d.badArc with
 | none => simp [build] at job
 | some setup =>
  have guarded : j∈OrdinaryCommonSplit.Caller.guardedJobs setup q := by simpa only [build] using job
  have paid : j∈OrdinaryCommonSplit.Caller.paidJobs setup q := by
   cases pre : DepthOne.pretest01 setup.ty setup.sy with
   | refused => simp [OrdinaryCommonSplit.Caller.guardedJobs,pre] at guarded
   | rejected => simp [OrdinaryCommonSplit.Caller.guardedJobs,pre] at guarded
   | found c =>
    cases c with
    | none => simp [OrdinaryCommonSplit.Caller.guardedJobs,pre] at guarded
    | some e => simpa [OrdinaryCommonSplit.Caller.guardedJobs,pre] using guarded
  have bounds:=Rule5LocalWork.built_job_numeric T S _ _ _ setup build q paid
  have max:=pair_max_le cap
  cases eq
  exact ⟨fun x hx=>by have:=bounds.2.2.1 x hx;omega,
   fun x hx=>by have:=bounds.2.2.2 x hx;omega⟩

theorem selected_forest_cap (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree}
 {i : RMAF.Vertex} {a b : Nat} {z : FinalSelection} (ch : CherryAt T i a b)
 (ad : admitted T S a b=true) (sel : selectFinal T S a b=some z) (q M : Nat)
 (cap : TreeCap M T) {p : Tree×Tree} {r : Nat}
 (mem : (p,r)∈queries actual (.forestJobs (forestJobs T q (selectedForestChildren S a b z)))) :
 PairCap M p.1 p.2 := by
 obtain ⟨j,hj,query⟩:=List.mem_flatMap.1 mem
 obtain ⟨hc,target,sources,rem⟩:=literal_job_binding hj
 have prop:=selected_child_proper ch ad sel hc
 rw [target,sources] at query
 exact frontier_cap actual (some T) j.child.sourceForest j.residual prop M cap p r query

theorem paid_requests_cap (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree}
 {a b : Nat} {R : Rule5PaidSelector.SelectedPaid T S}
 (built : Rule5PaidSelector.buildSelected T S a b=some R) (q M : Nat) (cap : PairCap M T S)
 {p : Tree×Tree} {r : Nat}
 (mem : (p,r)∈queries actual (.paidRequests (Rule5PaidSelector.requests R.geometry q))) :
 PairCap M p.1 p.2 := by
 obtain ⟨j,hj,query⟩:=List.mem_flatMap.1 mem
 have actualQuery:=(currentFrontier_member query).2.2
 have binding:=second_request_binding built hj
 obtain ⟨c,hc,request⟩:=List.mem_filterMap.1 hj
 obtain ⟨aff,branch,target,sources,residual⟩:=Rule5PaidSelector.requestFor_binding request
 apply frontier_cap actual (some j.target) j.sources j.residual binding.2.2 M _ p r actualQuery
 rw [target]
 unfold Rule5PaidSelector.opposite
 split
 · exact cap.1
 · exact cap.2

theorem selected_rule5_cap (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree}
 {i : RMAF.Vertex} {a b : Nat} (ch : CherryAt T i a b)
 (ad : admitted T S a b=true) {z : FinalSelection} (sel : selectFinal T S a b=some z)
 (q M : Nat) (cap : PairCap M T S) {p : Tree×Tree} {r : Nat}
 (mem : (p,r)∈queries actual (selectedTrace actual T S a b q z).calls) : PairCap (M+2) p.1 p.2 := by
 have lift (h : PairCap M p.1 p.2) : PairCap (M+2) p.1 p.2 :=
  ⟨treeCap_mono h.1 (by omega),treeCap_mono h.2 (by omega)⟩
 cases z with
 | «prefix» s => exact lift (selected_forest_cap actual ch ad sel q M cap.1 mem)
 | remaining d z =>
  cases z with
  | first u v => exact lift (selected_forest_cap actual ch ad sel q M cap.1 mem)
  | third u v => exact lift (selected_forest_cap actual ch ad sel q M cap.1 mem)
  | one edge => exact common_direct_cap actual T S a b d q M cap mem
  | second u v =>
   cases built : Rule5PaidSelector.buildSelected T S a b with
   | none => simp [selectedTrace,built,queries] at mem
   | some R =>
    apply lift
    apply paid_requests_cap actual built q M cap
    simpa [selectedTrace,built] using mem

theorem dispatch_rule5_cap (actual : GenericForest.FrontierWork.Ordinary) {T S : Tree}
 {i : RMAF.Vertex} {a b : Nat} (ch : CherryAt T i a b)
 (ad : admitted T S a b=true) (q M : Nat) (cap : PairCap M T S) {p : Tree×Tree} {r : Nat}
 (mem : (p,r)∈queries actual (dispatchTrace actual T S a b q).calls) : PairCap (M+2) p.1 p.2 := by
 obtain ⟨z,sel,_⟩:=final_classification_complete ch ad
 apply selected_rule5_cap actual ch ad sel q M cap
 simpa [dispatchTrace,sel] using mem
end OrdinaryDispatch.GlobalNumeric
