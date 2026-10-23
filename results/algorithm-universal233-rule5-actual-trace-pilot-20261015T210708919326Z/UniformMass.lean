import OuterMass
namespace Universal233.Rule5ActualTrace
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent
open CherryBranching Rule5Local Rule5Classification Rule5FinalClassification
open Rule5SourceOrientation Rule5OrdinaryDispatch

def base : Rat := 233/100
def gamma (c : Rat) : Rat := 2*c^(-1:Int)+4*c^(-4:Int)

theorem gamma_strict : gamma base<1 := by decide
theorem gamma_positive : 0≤gamma base := by decide

/-- This is mass of the actual ordinary callback frontier, including failed
and repeated occurrences, not merely a list of desired outer branch costs. -/
theorem selected_mass (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) {z : FinalSelection}
 (sel : selectFinal T S a b=some z) (q : Nat) :
 mass base q (queries actual (selectedTrace actual T S a b q z).calls)≤gamma base := by
 have fs := final_selected_sound ch ad sel
 cases z with
 | «prefix» s =>
   have bound := forest_jobs_mass actual T q (localChildren S a b s)
     (fun x hx => selected_child_proper ch ad sel hx) base (by decide)
   have vec := prefix_paid_vectors ch fs.1 fs.2
   have profile : costsMass base ((localChildren S a b s).map Child.paid)≤gamma base := by
     rw [vec]
     cases s <;> decide
   exact Rat.le_trans bound profile
 | remaining d z =>
   cases z with
   | first u v =>
     have bound := forest_jobs_mass actual T q (firstChildren S a b d)
       (fun x hx => selected_child_proper ch ad sel hx) base (by decide)
     have vec := (selected_child_states ch fs.1 fs.2.1).1
     rw [vec] at bound
     exact Rat.le_trans bound (by decide : costsMass base [1,2]≤gamma base)
   | third u v =>
     have bound := forest_jobs_mass actual T q (thirdChildren S a b d)
       (fun x hx => selected_child_proper ch ad sel hx) base (by decide)
     have vec := (selected_child_states ch fs.1 fs.2.1).2.1
     rw [vec] at bound
     exact Rat.le_trans bound (by decide : costsMass base [1,2]≤gamma base)
   | one edge =>
     exact Rat.le_trans (common_mass actual T S a b d q base (by decide))
       (by decide : 2*base^(-1:Int)≤gamma base)
   | second u v =>
     cases built : Rule5PaidSelector.buildSelected T S a b with
     | none => simpa [selectedTrace,built,queries,mass,Universal233.PaidQueries.actualQueryMass] using gamma_positive
     | some R =>
       have bound := paid_requests_mass actual built q base (by decide)
       simpa [selectedTrace,built] using Rat.le_trans bound
         (by decide : base^(-1:Int)+3*base^(-2:Int)≤gamma base)

theorem dispatch_mass (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (q : Nat) :
 mass base q (queries actual (dispatchTrace actual T S a b q).calls)≤gamma base := by
 obtain ⟨z,sel,_⟩ := final_classification_complete ch ad
 simpa [dispatchTrace,sel] using selected_mass actual ch ad sel q

theorem dispatch_mass_strict (actual : Ordinary) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true) (q : Nat) :
 mass base q (queries actual (dispatchTrace actual T S a b q).calls)<1 :=
 Rat.lt_of_le_of_lt (dispatch_mass actual ch ad q) gamma_strict

/-- Explicit ordinary charges over the actual source-level callback frontier.
This omits no failed/duplicate call. Guard/pretest/materialization/forest local
overhead and compiled-machine/bit costs are separate obligations. -/
def ordinaryWork (actual : Ordinary) (W : GenericForest.FrontierWork.OrdinaryWork) (r : Receipt) : Nat :=
 GenericForest.FrontierWork.queryWork W (queries actual r.calls)
end Universal233.Rule5ActualTrace
