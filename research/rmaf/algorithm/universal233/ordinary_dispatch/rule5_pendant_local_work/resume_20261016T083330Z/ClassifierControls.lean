import FinalClassifierWork
import PendantWorkControls
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching Rule5Classification Rule5FinalClassification

def fork4 : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def comb4 : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3)
def rejectOption (_ : Nat) : CheckReceipt (Option Nat) :=⟨none,3,[]⟩
def finalControl (T S : Tree) (a b : Nat) : Bool :=
 decide ((finalMeter fee T S a b).value=selectFinal T S a b) &&
 decide ((finalMeter fee T S a b).work≤finalBudget (leaves T).length (leaves S).length 7) &&
 decide ((finalMeter fee T S a b).calls.length≤7*(leaves S).length+3+(2*(leaves S).length)*(2*(leaves S).length))

def classifierControls : List (String×Bool) :=
 [("incident_leaf_null",decide ((incidentMeter (.leaf 0) []).value=[])),
  ("root_short_circuit",decide ((incidentAtMeter fork4 [0,3] []).value=false) &&decide ((incidentAtMeter fork4 [0,3] []).work=1)),
  ("invalid_subtree",decide ((subtreeMeter (.leaf 0) [true]).value=none)),
  ("one_boundary",decide ((boundaryMeter (.node (.leaf 0) (.leaf 1)) [0] 1).value=some (.one [false]))),
  ("two_outgoing",decide ((boundaryMeter fork4 [0,3] 1).value=some (.second [false,true] [true,false]))),
  ("two_outgoing_swapped",decide ((boundaryMeter fork4 [0,3] 2).value=some (.second [true,false] [false,true]))),
  ("first_boundary",decide ((boundaryMeter comb4 [0,2] 1).value=some (.first [false,false,true] [false]))),
  ("third_boundary",decide ((boundaryMeter comb4 [0,2] 3).value=some (.third [false] [false,false,true]))),
  ("bad_equal_skips_primitive",decide ((badAtMeter fee sixT sixS [false] [false]).calls=[])),
  ("bad_unequal_keeps_primitive",decide ((badAtMeter fee sixT sixS [false] [true]).calls.length=1)),
  ("duplicate_failed_occurrences",decide ((optionsMeter rejectOption [0,0]).value=(optionsMeter rejectOption [0]).value) &&
   decide ((optionsMeter rejectOption [0,0]).work>(optionsMeter rejectOption [0]).work)),
  ("full_filter_after_head",let m:=selectLargeMeter fee sixT sixS 0 1
   decide (m.value=selectLarge sixT sixS 0 1) &&decide (m.calls.length=(cuts sixS 0 1).length)),
  ("actual_admitted_final",finalControl sixT sixS 0 1),
  ("missing_endpoints_final",finalControl sixT sixS 90 91),
  ("duplicate_labels_final",finalControl repeated repeated 0 0),
  ("coincident_endpoints_final",finalControl smallT smallS 1 1),
  ("leaf_final",finalControl (.leaf 0) (.leaf 0) 0 1),
  ("strict_P_refused_final",let m:=finalMeter fee repeated repeated 0 0
   decide (m.value=none) &&decide (m.work>(partitionMeter repeated 0 0).work)),
  ("omitted_boundary_evaluation_caught",let m:=boundaryMeter comb4 [0,2] 1
   let corrupt:={m with work:=0}
   decide (corrupt.value=m.value) &&decide (corrupt.work≠m.work))]
#eval classifierControls
#eval ("PASS_ACTUAL_CLASSIFIER_CONTROLS",classifierControls.length,classifierControls.all Prod.snd)
end Universal233.Rule5PendantLocalWork
