import BranchMetadata
namespace Universal233.Rule5OrdinaryDispatch
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent
open CherryBranching Rule5Local Rule5Classification Rule5FinalClassification Rule5SourceOrientation

def selectedForestChildren (S : Tree) (a b : Nat) : FinalSelection → List Child
 | .prefix s => localChildren S a b s
 | .remaining d (.first _ _) => firstChildren S a b d
 | .remaining d (.third _ _) => thirdChildren S a b d
 | _ => []

theorem selected_forest_facts {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {z : FinalSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (sel : selectFinal T S a b=some z)
 {c : Child} (hc : c∈selectedForestChildren S a b z) : ChildFacts S c ∧ OriginalCutWitness S c := by
 cases z with
 | «prefix» s =>
   have fs := final_selected_sound ch ad sel
   exact ⟨prefix_facts ch fs.1 fs.2 hc,prefix_cut_witness ch fs.1 fs.2 hc⟩
 | remaining d z =>
   cases z with
   | first u v => exact ⟨first_facts ch ad sel hc,ordinary_branch_cut_witness ch ad (first_subbranches ch ad sel hc)⟩
   | third u v => exact ⟨third_facts ch ad sel hc,ordinary_branch_cut_witness ch ad (third_subbranches ch ad sel hc)⟩
   | one edge => simp [selectedForestChildren] at hc
   | second u v => simp [selectedForestChildren] at hc

theorem selected_forest_job_binding {T S : Tree} {i : RMAF.Vertex} {a b q : Nat} {z : FinalSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (sel : selectFinal T S a b=some z)
 {j : ForestJob} (mem : j∈forestJobs T q (selectedForestChildren S a b z)) :
 j.target=some T ∧ j.sources=OutputState.sourceForest S j.child.partition ∧
 partitionCheck (leaves S) j.child.partition=true ∧ pairwiseEmbeddings S j.child.partition=true ∧
 j.residual<q ∧ ∃br : SourceBranch,br.child=j.child ∧ br.originalCuts.Nodup ∧
 (∀e,e∈br.originalCuts → Valid S e ∧ e≠[]) ∧ br.originalCuts.length+j.residual=q := by
 exact actual_job_full_payment (fun _ hc => (selected_forest_facts ch ad sel hc).1)
   (fun _ hc => (selected_forest_facts ch ad sel hc).2) mem

/-- The descendant ordinary callback may only observe budgets at most the
literal forest residual; that residual is strictly below the original q. -/
theorem selected_forest_callback_locality {T S : Tree} {i : RMAF.Vertex} {a b q : Nat} {z : FinalSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (sel : selectFinal T S a b=some z)
 {j : ForestJob} (mem : j∈forestJobs T q (selectedForestChildren S a b z))
 (f g : Ordinary) (eq : ∀t s r,r<q → f t s r=g t s r) :
 GenericForest.solve f j.target j.sources j.residual=GenericForest.solve g j.target j.sources j.residual := by
 have strict := (selected_forest_job_binding ch ad sel mem).2.2.2.2.1
 apply GenericForest.LocalIH.solve_congr_budget f g j.residual
 intro t s r le
 exact eq t s r (by omega)

theorem selected_forest_vectors {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {z : FinalSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (sel : selectFinal T S a b=some z) :
 (selectedForestChildren S a b z).map Child.paid=
 match z with
 | .prefix (.large _) => [2]
 | .prefix (.two _) => [2,2,2,2,2]
 | .prefix (.outside _) => [2,2,2,2,2]
 | .remaining _ (.first _ _) => [1,2]
 | .remaining _ (.third _ _) => [1,2]
 | _ => [] := by
 have fs := final_selected_sound ch ad sel
 cases z with
 | «prefix» s => exact prefix_paid_vectors ch fs.1 fs.2
 | remaining d z =>
   have states := selected_child_states ch fs.1 fs.2.1
   cases z with
   | first u v => exact states.1
   | third u v => exact states.2.1
   | one edge => rfl
   | second u v => rfl

/-- Actual common.one ordinary jobs carry the unchanged full separator debit. -/
theorem common_one_job_binding (T S : Tree) (a b q : Nat) (d : BadSelection)
 (j : OrdinaryCommonSplit.Caller.Job) (mem : j∈Rule5CommonSelector.commonJobs T S a b d q) :
 DepthOne.proper j.T j.S=true ∧ j.budget<q ∧ q-j.budget=1 :=
 Rule5CommonOrdinary.callback_jobs_below T S a b d q j mem

/-- The paid.second request retains its selected source geometry, full actual
source forest, complete original cut list and current residual. No refund. -/
theorem second_request_binding {T S : Tree} {a b q : Nat}
 {R : Rule5PaidSelector.SelectedPaid T S} (built : Rule5PaidSelector.buildSelected T S a b=some R)
 {Q : Rule5PaidSelector.PaidRequest} (mem : Q∈Rule5PaidSelector.requests R.geometry q) :
 Q.residual<q ∧ Q.residual+Q.branch.originalCuts.length=q ∧
 ForestState.proper (some Q.target) Q.sources=true := by
 have strict := Rule5PaidOrdinary.request_decrease R mem
 have paid := Rule5PaidOrdinary.request_payment_exact R mem
 obtain ⟨c,hc,hQ⟩ := List.mem_filterMap.1 mem
 obtain ⟨aff,branch,target,sources,residual⟩ := Rule5PaidSelector.requestFor_binding hQ
 have proper := Rule5PaidSelector.full_state_proper R.geometry c (Rule5PaidSelector.selected_actual_guards built c hc)
 exact ⟨strict,paid,by simpa [target,sources] using proper⟩

theorem child_list_callback_locality (f g : Ordinary) {T S : Tree} {q : Nat} {cs : List Child}
 (positive : ∀c,c∈cs → 0<c.paid) (eq : ∀t s r,r<q → f t s r=g t s r) :
 runChildren f T S q cs=runChildren g T S q cs := by
 unfold runChildren childAnswers
 congr 1
 apply List.filterMap_congr
 intro c hc
 cases hr : remaining q c with
 | none => simp [childCall,hr]
 | some r =>
   have strict := (remaining_strict (positive c hc) hr).1
   have he := GenericForest.LocalIH.solve_congr_budget f g r
     (fun t s b hb => eq t s b (by omega)) (some T) c.sourceForest
   simpa [childCall,hr,OrdinaryDispatch.forestChild] using he
end Universal233.Rule5OrdinaryDispatch
