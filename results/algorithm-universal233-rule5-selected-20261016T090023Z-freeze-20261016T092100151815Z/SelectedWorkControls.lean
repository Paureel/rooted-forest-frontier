import ForestArmBinding
namespace Universal233.Rule5SelectedLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork
open CherryBranching CoreWork Rule5Classification Rule5FinalClassification Rule5SourceOrientation
open GenericForest.CheckCorrespondence

def t2 : Tree :=.node (.leaf 0) (.leaf 1)
def t3 : Tree :=.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def s3 : Tree :=.node (.leaf 0) (.node (.leaf 2) (.leaf 1))
def repeated3 : Tree :=.node (.leaf 0) (.node (.leaf 0) (.leaf 1))
def noOrdinary : Ordinary :=fun _ _ _=>none
def forestFee (_ : ForestQuery) : Nat :=7
def agreementFee (_ : Forest) : Nat :=11
def bsel : BadSelection :=⟨[true],[false],0⟩
def arbitraryChild : Child :=⟨[],[],0⟩
def allCheck (_ : Forest) : Measured Bool :=⟨true,1⟩

def pendantControl (S : Tree) (a b : Nat) : Bool :=
 decide ((pendantChildMeter S a b).value=pendantChild S a b) &&
 decide ((pendantChildMeter S a b).work≤pendantChildBudget (leaves S).length)
def childrenControl (S : Tree) (a b p q : Nat) : Bool :=
 decide ((fiveChildrenMeter S a b p q).value=fiveChildren S a b p q) &&
 decide ((fiveChildrenMeter S a b p q).work≤fiveChildrenBudget (leaves S).length)
def executionControl (cs : List Child) (q : Nat) : Bool :=
 let r:=runChildrenMeter noOrdinary forestFee agreementFee t2 t2 q cs
 decide (r.value=Rule5OrdinaryDispatch.runChildren noOrdinary t2 t2 q cs) &&
 decide (r.localWork≤(11+3*(leaves t2).length+16)*cs.length+4) &&
 decide (r.recursiveWork=(r.calls.map forestFee).sum)

def selectedControls : List (String×Bool) :=
 [("restrict_none_none",decide ((meterRestrict [] t2).value=none)),
  ("restrict_some_none",decide ((meterRestrict [0] t2).value=some (.leaf 0))),
  ("restrict_none_some",decide ((meterRestrict [1] t2).value=some (.leaf 1))),
  ("restrict_some_some",decide ((meterRestrict [0,1] t2).value=some t2)),
  ("restrict_repeated_missing",decide ((meterRestrict [0,0,9] repeated3).value=some (.node (.leaf 0) (.leaf 0)))),
  ("empty_blocks_counted",decide ((sourceForestMeter t2 [[],[]]).value=(sourceForestMeter t2 [[]]).value) &&
   decide ((sourceForestMeter t2 [[],[]]).work>(sourceForestMeter t2 [[]]).work)),
  ("duplicate_materialized_blocks",decide ((sourceForestMeter t2 [[0],[0]]).value=[.leaf 0,.leaf 0])),
  ("malformed_partition_value",decide ((makeChildMeter t2 [[9],[],[0],[0]] 2).value=makeChild t2 [[9],[],[0],[0]] 2)),
  ("pendant_literal",pendantControl s3 0 1),
  ("pendant_missing",pendantControl s3 80 81),
  ("pendant_coincident",pendantControl s3 1 1),
  ("pendant_repeated",pendantControl repeated3 0 1),
  ("pair_missing_unit_scope",decide ((pairChildMeter s3 80 81).value=pairChild s3 80 81) &&
   decide ((pairChildMeter s3 80 81).work≤pairChildBudget (leaves s3).length)),
  ("five_literal",childrenControl s3 0 1 2 1),
  ("sibling_root_refuses",decide ((siblingEndpointMeter t2 []).value=none)),
  ("sibling_invalid_refuses",decide ((siblingEndpointMeter t2 [true,true]).value=none)),
  ("sibling_both_orientations",decide ((siblingEndpointMeter t2 [true]).value=some 0) &&decide ((siblingEndpointMeter t2 [false]).value=some 1)),
  ("first_children_literal",decide ((firstChildrenMeter t2 0 1 bsel).value=firstChildren t2 0 1 bsel)),
  ("third_children_literal",decide ((thirdChildrenMeter t2 0 1 bsel).value=thirdChildren t2 0 1 bsel)),
  ("local_large_literal",decide ((localChildrenMeter s3 0 1 (.large [])).value=localChildren s3 0 1 (.large []))),
  ("score_length_empty_tie",decide ((bestLengthMeter allCheck [[[0]],[]]).value=some [])),
  ("execution_empty",executionControl [] 0),
  ("execution_refused",executionControl [singletonChild t2 0] 0 &&decide ((runChildrenMeter noOrdinary forestFee agreementFee t2 t2 0 [singletonChild t2 0]).calls.length=0)),
  ("execution_duplicate_calls",let cs:=[singletonChild t2 0,singletonChild t2 0]
   let r:=runChildrenMeter noOrdinary forestFee agreementFee t2 t2 1 cs
   executionControl cs 1 &&decide (r.calls.length=2) &&decide (r.agreementChecks.length=2)),
  ("later_refusal_counted",let a:=runChildrenMeter noOrdinary forestFee agreementFee t2 t2 1 [singletonChild t2 0]
   let b:=runChildrenMeter noOrdinary forestFee agreementFee t2 t2 1 [singletonChild t2 0,arbitraryChild]
   decide (a.value=b.value) &&decide (b.calls.length=2) &&decide (b.agreementChecks.length=1) &&decide (a.localWork<b.localWork)),
  ("corrupted_zero_work_caught",let m:=pendantChildMeter s3 0 1
   let corrupt:={m with work:=0}
   decide (m.value=corrupt.value) &&decide (m.work≠corrupt.work))]
#eval selectedControls
#eval ("PASS_LITERAL_SELECTED_BODY_CONTROLS",selectedControls.length,selectedControls.all Prod.snd)
end Universal233.Rule5SelectedLocalWork
