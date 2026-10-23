import SelectedInterfaces
import Hard2Program
import BoundedFrontier
namespace Universal233.Rule5ActualTrace
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent
open CherryBranching Rule5Local Rule5Classification Rule5FinalClassification
open Rule5SourceOrientation Rule5OrdinaryDispatch
abbrev Forest := List (List Nat)
abbrev Ordinary := Tree→Tree→Nat→Option Forest
abbrev Query := GenericForest.FrontierWork.Query

open OrdinaryCommonSplit.Caller in
def finishPaid (d : Setup) (q : Nat) (FY FN : Forest) (answers : List (Option Forest)) : Option Forest :=
 match answers with
 | [some FX,some FM] =>
   match reconstruct d FX FY FM FN with
   | none => none
   | some G => if G.length-1≤q then some G else none
 | _ => none

structure CommonReceipt where
 value : Option (Option Forest)
 calls : List OrdinaryCommonSplit.Caller.Job

/-- The source builder, outside guards and the literal TWO DIRECT ordinary
evaluations. Failure of either callback does not remove its occurrence. -/
def commonTrace (actual : Ordinary) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) : CommonReceipt :=
 match OrdinaryCommonSplit.Source.buildSetup T S (subtreeLabels S d.badArc)
     (Rule5CommonSelector.outsideLabels S a b d) d.badArc with
 | none => ⟨none,[]⟩
 | some setup =>
   match DepthOne.pretest01 setup.ty setup.sy with
   | .found (some p) =>
     let FY := DepthOne.forest setup.sy (some p)
     match OrdinaryCommonSplit.Caller.outsideReply setup FY with
     | none => ⟨some none,[]⟩
     | some FN =>
       let js := OrdinaryCommonSplit.Caller.paidJobs setup q
       let answers := js.map fun j => actual j.T j.S j.budget
       ⟨some (finishPaid setup q FY FN answers),js⟩
   | _ => ⟨none,[]⟩

theorem common_value (actual : Ordinary) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) :
 (commonTrace actual T S a b d q).value=Rule5CommonSelector.runCommon T S a b d q actual := by
 unfold commonTrace Rule5CommonSelector.runCommon OrdinaryCommonSplit.Source.runSource
 cases build : OrdinaryCommonSplit.Source.buildSetup T S (subtreeLabels S d.badArc)
     (Rule5CommonSelector.outsideLabels S a b d) d.badArc with
 | none => rfl
 | some setup =>
   cases pre : DepthOne.pretest01 setup.ty setup.sy with
   | refused => simp [OrdinaryCommonSplit.Caller.runGuarded,pre]
   | rejected => simp [OrdinaryCommonSplit.Caller.runGuarded,pre]
   | found c =>
     cases c with
     | none => simp [OrdinaryCommonSplit.Caller.runGuarded,pre]
     | some p =>
       cases outside : OrdinaryCommonSplit.Caller.outsideReply setup (DepthOne.forest setup.sy (some p)) <;>
         simp [OrdinaryCommonSplit.Caller.runGuarded,OrdinaryCommonSplit.Caller.runWithOutside,
           OrdinaryCommonSplit.Caller.runPaid,finishPaid,pre,outside]

theorem common_calls (actual : Ordinary) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) :
 (commonTrace actual T S a b d q).calls=Rule5CommonSelector.commonJobs T S a b d q := by
 unfold commonTrace Rule5CommonSelector.commonJobs OrdinaryCommonSplit.Source.sourceJobs
 cases build : OrdinaryCommonSplit.Source.buildSetup T S (subtreeLabels S d.badArc)
     (Rule5CommonSelector.outsideLabels S a b d) d.badArc with
 | none => rfl
 | some setup =>
   cases pre : DepthOne.pretest01 setup.ty setup.sy with
   | refused => simp [OrdinaryCommonSplit.Caller.guardedJobs,pre]
   | rejected => simp [OrdinaryCommonSplit.Caller.guardedJobs,pre]
   | found c =>
     cases c with
     | none => simp [OrdinaryCommonSplit.Caller.guardedJobs,pre]
     | some p =>
       have found := OrdinaryCommonSplit.Caller.found_one_minimum setup.ty setup.sy p pre
       obtain ⟨FN,outside,_,_,_⟩ := OrdinaryCommonSplit.Caller.outsideReply_spec setup
         (DepthOne.forest setup.sy (some p)) found.1 found.2.1
       simp [OrdinaryCommonSplit.Caller.guardedJobs,pre,outside]

def directQueries (js : List OrdinaryCommonSplit.Caller.Job) : List Query :=
 js.map fun j => ((j.T,j.S),j.budget)

theorem common_direct_progress (actual : Ordinary) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat)
 {p : Tree×Tree} {r : Nat} (mem : (p,r)∈directQueries (commonTrace actual T S a b d q).calls) :
 DepthOne.proper p.1 p.2=true ∧ r<q ∧ q-r=1 := by
 obtain ⟨j,hj,eq⟩ := List.mem_map.1 mem
 have hj' : j∈Rule5CommonSelector.commonJobs T S a b d q := by rw [←common_calls actual];exact hj
 have progress := Rule5CommonSelector.selected_one_job_progress T S a b d q j hj'
 cases eq
 exact progress
end Universal233.Rule5ActualTrace
