import MassTransfer
namespace Universal233.Rule5ActualTrace
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent
open CherryBranching Rule5Local Rule5Classification Rule5FinalClassification
open Rule5SourceOrientation Rule5OrdinaryDispatch GenericForest.FrontierWork
open Rule5Case322 Case322PaidGuard Rule5PaidSelector

def costsMass (c : Rat) (ds : List Nat) : Rat := (ds.map (debit c)).sum

theorem remaining_payment {q r : Nat} {c : Child} (hr : remaining q c=some r) :
 r≤q ∧ q-r=c.paid := by
 unfold remaining at hr
 split at hr
 · have eq := Option.some.inj hr
   omega
 · contradiction

theorem forest_jobs_mass (actual : Ordinary) (T : Tree) (q : Nat) (cs : List Child)
 (proper : ∀x,x∈cs →ForestState.proper (some T) x.sourceForest=true) (c : Rat) (hc : 2≤c) :
 mass c q (queries actual (.forestJobs (forestJobs T q cs)))≤costsMass c (cs.map Child.paid) := by
 induction cs with
 | nil => simp [queries,forestJobs,mass,Universal233.PaidQueries.actualQueryMass,costsMass]
 | cons x xs ih =>
   have tail := ih (fun y hy => proper y (by simp [hy]))
   have nonneg : 0≤debit c x.paid := Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c))
   cases rem : remaining q x with
   | none =>
     have step := Rat.le_trans tail (show costsMass c (xs.map Child.paid)≤debit c x.paid+costsMass c (xs.map Child.paid) by grind)
     simpa [queries,forestJobs,jobFor,rem,costsMass] using step
   | some r =>
     have pay := remaining_payment rem
     have head := forest_mass_paid actual (some T) x.sourceForest pay.1 (proper x (by simp)) c hc
     rw [pay.2] at head
     have sum := Universal233.SourceCoverage.qadd_le_add head tail
     simpa [queries,forestJobs,jobFor,rem,costsMass,mass_append] using sum

theorem selected_child_proper {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {z : FinalSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (sel : selectFinal T S a b=some z)
 {x : Child} (hx : x∈selectedForestChildren S a b z) : ForestState.proper (some T) x.sourceForest=true := by
 have prop := properPair_parts (admitted_parts ad).1
 have facts := (selected_forest_facts ch ad sel hx).1
 rw [facts.2.2.2.1]
 exact OutputState.sourceForest_proper T S x.partition prop.1 prop.2.1 prop.2.2 facts.1

theorem paid_list_mass (actual : Ordinary) {T S : Tree} (D : LiteralGeometry T S) (q : Nat)
 (cs : List Branch) (guards : ∀x,x∈cs →currentGuard T S x=true) (c : Rat) (hc : 2≤c) :
 mass c q (queries actual (.paidRequests (cs.filterMap (requestFor T S q))))≤costsMass c (cs.map paid) := by
 induction cs with
 | nil => simp [queries,mass,Universal233.PaidQueries.actualQueryMass,costsMass]
 | cons x xs ih =>
   have tail := ih (fun y hy => guards y (by simp [hy]))
   by_cases affordable : paid x≤q
   · have head := current_mass_paid actual (some (opposite T S x)) (Rule5Case322.sourceForest T S x)
       (show q-paid x≤q by omega) (full_state_proper D x (guards x (by simp))) c hc
     have pay : q-(q-paid x)=paid x := by omega
     rw [pay] at head
     have sum := Universal233.SourceCoverage.qadd_le_add head tail
     simpa [queries,requestFor,affordable,costsMass,mass_append] using sum
   · have nonneg : 0≤debit c (paid x) := Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c))
     have sum := Rat.le_trans tail (show costsMass c (xs.map paid)≤debit c (paid x)+costsMass c (xs.map paid) by grind)
     simpa [queries,requestFor,affordable,costsMass] using sum

theorem paid_requests_mass (actual : Ordinary) {T S : Tree} {a b : Nat}
 {R : SelectedPaid T S} (built : buildSelected T S a b=some R) (q : Nat) (c : Rat) (hc : 2≤c) :
 mass c q (queries actual (.paidRequests (requests R.geometry q)))≤c^(-1:Int)+3*c^(-2:Int) := by
 have bound := paid_list_mass actual R.geometry q (guardedPlan R.geometry)
   (fun x hx => selected_actual_guards built x hx) c hc
 change mass c q (queries actual (.paidRequests (requests R.geometry q)))≤_ at bound
 have nonneg : 0≤c^(-2:Int) := Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c))
 rcases guarded_cost_classes R.geometry with costs | ⟨d,hd,costs⟩
 · rw [costs] at bound
   simp only [costsMass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,debit,Rat.add_zero] at bound
   grind
 · have mono := Universal233.PaidQueries.negpow_antitone c hc 2 d hd
   rw [costs] at bound
   simp only [costsMass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,debit,Rat.add_zero] at bound
   grind

theorem common_mass (actual : Ordinary) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat)
 (c : Rat) (hc : 2≤c) :
 mass c q (directQueries (commonTrace actual T S a b d q).calls)≤2*c^(-1:Int) := by
 rw [common_calls]
 unfold Rule5CommonSelector.commonJobs OrdinaryCommonSplit.Source.sourceJobs
 have pos : 0≤2*c^(-1:Int) := Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c)))
 cases build : OrdinaryCommonSplit.Source.buildSetup T S (subtreeLabels S d.badArc)
     (Rule5CommonSelector.outsideLabels S a b d) d.badArc with
 | none => simpa [directQueries,mass,Universal233.PaidQueries.actualQueryMass] using pos
 | some setup =>
   cases pre : DepthOne.pretest01 setup.ty setup.sy with
   | refused => simpa [OrdinaryCommonSplit.Caller.guardedJobs,pre,directQueries,mass,Universal233.PaidQueries.actualQueryMass] using pos
   | rejected => simpa [OrdinaryCommonSplit.Caller.guardedJobs,pre,directQueries,mass,Universal233.PaidQueries.actualQueryMass] using pos
   | found cut =>
     cases cut with
     | none => simpa [OrdinaryCommonSplit.Caller.guardedJobs,pre,directQueries,mass,Universal233.PaidQueries.actualQueryMass] using pos
     | some p =>
       by_cases zero : q=0
       · simpa [OrdinaryCommonSplit.Caller.guardedJobs,pre,OrdinaryCommonSplit.Caller.paidJobs,zero,directQueries,mass,Universal233.PaidQueries.actualQueryMass] using pos
       · have eq := OrdinaryCommonSplit.Caller.callback_mass_eq c setup q (by omega)
         change _≤2*c^(-1:Int)
         simp only [OrdinaryCommonSplit.Caller.guardedJobs,pre]
         have bound : OrdinaryCommonSplit.Caller.callbackMass c setup q≤2*c^(-1:Int) := by rw [eq];exact Rat.le_refl
         simpa [directQueries,mass,Universal233.PaidQueries.actualQueryMass,OrdinaryCommonSplit.Caller.callbackMass,List.map_map,Function.comp_def] using bound
end Universal233.Rule5ActualTrace
