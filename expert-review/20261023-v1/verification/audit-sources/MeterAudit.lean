import WholeFunctional
import CompletePolynomialExplicit
namespace SourceMeterAudit20261022
open RMAF ForestState Universal233 OrdinaryDispatch
open GenericForest.FrontierWork OrdinaryDispatch.WorkRecursion

theorem every_recorded_cell_charged (xs : List Query) :
    queryWork (fun _ _ _=>1) xs=xs.length := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    change 1+queryWork (fun _ _ _=>1) xs=xs.length+1
    omega

theorem duplicate_cells (W : OrdinaryWork) (x : Query) :
    queryWork W [x,x]=W x.1.1 x.1.2 x.2+W x.1.1 x.1.2 x.2 := by
  simp [queryWork]

def T : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def S : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def refusing : GenericForest.FrontierWork.Ordinary := fun _ _ _=>none
def underlying : Nat→Tree→Tree→Option (List (List Nat)) := fun _ _ _=>some [[0],[1],[2],[3]]

theorem singleton_proper : DepthOne.proper T S=true := by decide +kernel

theorem singleton_failed_record_retained :
    frontier refusing (some T) [S] 0=[((T,S),0)] := by decide +kernel

theorem singleton_refuses : GenericForest.solve refusing (some T) [S] 0=none := by decide +kernel

theorem equalbudget_cutoff_refuses : FastOrdinary.cutoff underlying 0 T S 0=none := by decide +kernel

theorem equalbudget_underlying_succeeds : underlying 0 T S≠none := by decide +kernel

theorem equalbudget_record_retained :
    frontier (FastOrdinary.cutoff underlying 0) (some T) [S] 0=[((T,S),0)] := by decide +kernel

theorem equalbudget_bill_retained :
    queryWork (fun _ _ _=>7)
      (frontier (FastOrdinary.cutoff underlying 0) (some T) [S] 0)=7 := by decide +kernel

def hardT : Tree := .node (.node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3)) (.leaf 4)) (.leaf 5)
def hardS : Tree := .node (.node (.node (.node (.node (.leaf 2) (.leaf 4)) (.leaf 0)) (.leaf 3)) (.leaf 1)) (.leaf 5)
def hardStage : String := match DepthOne.pretest01 hardT hardS with
 | .refused=>"pretest.refused"
 | .found _=>"pretest.found"
 | .rejected=>match FastOrdinary.early hardT hardS with
  | .common _ _=>"common"
  | .one _ _=>"one"
  | .high _ _=>"high"
  | .rule4Forward _=>"rule4.forward"
  | .rule4Reverse _=>"rule4.reverse"
  | .hard2 _ _=>"hard2"
  | .refused=>"early.refused"
def queries (q : Nat) := (ordinaryStepTrace FastOrdinary.solve q hardT hardS).queries
#eval ("SOURCE_METER_FIXTURE",DepthOne.proper hardT hardS,hardStage,
  (queries 0).length,queries 0,(queries 2).length,queries 2)

theorem source_counter_actual_step (q : Nat) (T S : Tree) :
    CompleteSource.completeSourceCounter q T S=
      (CompleteSource.ordinaryCompleteStepSource
        (fun t s r=>CompleteSource.completeSourceCounter r t s) q T S).work :=
  CompleteSource.completeSourceCounter_actual_step q T S

def commonT : Tree := .node hardT (.node (.leaf 6) (.leaf 7))
def commonS : Tree := .node hardS (.node (.leaf 6) (.leaf 7))
def commonQueries := (ordinaryStepTrace FastOrdinary.solve 0 commonT commonS).queries
#eval ("SOURCE_COMMON_FIXTURE",DepthOne.proper commonT commonS,commonStage commonT commonS,
  commonQueries.length,commonQueries.map (fun x=>(x.2,(leaves x.1.1).length)),
  (leaves commonT).length)

theorem actual_common_equalbudget_retained :
    commonStage commonT commonS=true ∧ commonQueries.length=1 ∧
    queryWork (fun _ _ _=>7) commonQueries=7 ∧
    (commonQueries.map (fun x=>(x.2,(leaves x.1.1).length)))=[(0,7)] := by decide +kernel

#eval ("SOURCE_COMMON_VALUE",FastOrdinary.solve 0 commonT commonS)

#print axioms every_recorded_cell_charged
#print axioms singleton_failed_record_retained
#print axioms equalbudget_bill_retained
end SourceMeterAudit20261022
