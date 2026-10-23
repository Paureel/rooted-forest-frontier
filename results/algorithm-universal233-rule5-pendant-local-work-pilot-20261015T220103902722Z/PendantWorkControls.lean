import AdmittedEnvelope
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching

def smallT : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def smallS : Tree := .node (.leaf 0) (.node (.leaf 2) (.leaf 1))
def repeated : Tree := .node (.leaf 0) (.leaf 0)
-- Exact completed DEVELOPMENT fixture from frozen Rule5PreControls.
def sixT : Tree := .node (.node (.node (.node (.leaf 14) (.node (.leaf 0) (.leaf 1))) (.leaf 15)) (.leaf 2)) (.leaf 16)
def sixS : Tree := .node (.node (.node (.leaf 0) (.node (.leaf 14) (.node (.leaf 15) (.leaf 16)))) (.leaf 2)) (.leaf 1)
def fee (_ : CheckRequest) : Nat :=7

def treeControl (T : Tree) (a b : Nat) : Bool :=
 decide ((verticesMeter T).value=vertices T) &&
 decide ((verticesMeter T).value.length+1=2*(leaves T).length) &&
 decide ((minimalMeter [a,b] T).value=minimalVertices [a,b] T) &&
 decide ((minimalMeter [a,b] T).work≤minimalBudget 2 (leaves T).length) &&
 decide ((cutsMeter T a b).value=cuts T a b) &&
 decide ((cutsMeter T a b).work≤cutsBudget (leaves T).length) &&
 decide ((partitionMeter T a b).value=pendantPartition T a b) &&
 decide ((partitionMeter T a b).work≤partitionBudget (leaves T).length)

def pairControl (T S : Tree) (a b : Nat) : Bool :=
 decide ((earlierMeter T S).value=Rule5Local.earlierClear T S) &&
 decide ((admittedRule4Meter T S).value=Rule5Local.rule4 T S) &&
 decide ((admittedMeter fee T S a b).value=Rule5Local.admitted T S a b) &&
 decide ((admittedMeter fee T S a b).work≤admittedBudget (leaves T).length (leaves S).length 7) &&
 decide ((admittedMeter fee T S a b).calls.length≤2*(leaves S).length+3)

def controls : List (String×Bool) :=
 [("leaf",treeControl (.leaf 0) 0 1),("unbalanced",treeControl smallT 0 1),
  ("repeated",treeControl repeated 0 0),("missing",treeControl smallS 8 9),
  ("coincident",treeControl smallS 1 1),
  ("address_scans",decide ((containsAddressMeter [false] [[],[true],[false]]).value=true) &&
     decide ((containsAddressMeter [false] [[],[true],[false]]).work≤(2*2+2)*3+1)),
  ("invalid_subtree",decide ((subtreeLabelsMeter (.leaf 0) [false]).value=[])),
  ("empty_root",decide ((subtreeLabelsMeter smallT []).value=leaves smallT)),
  ("pair_small",pairControl smallT smallS 0 1),
  ("pair_refused",pairControl repeated repeated 0 0),
  ("actual_admitted",pairControl sixT sixS 0 1 &&(admittedMeter fee sixT sixS 0 1).value),
  ("all_five_primitive_occurrences",decide ((admittedMeter fee sixT sixS 0 1).calls.length=5)),
  ("omitted_check_same_value",let r:=admittedMeter fee sixT sixS 0 1
    let bad:={r with calls:=r.calls.tail}
    decide (bad.value=r.value) &&decide (bad.calls.length≠5)),
  ("strict_P_refusal_paid",let r:=admittedMeter fee repeated repeated 0 0
    !r.value &&decide ((partitionMeter repeated 0 0).work<r.work)),
  ("miss_scan_retained",let a:=containsAddressMeter [true,true] [[],[false]]
    let b:=containsAddressMeter [true,true] [[]]
    decide (a.value=b.value) &&decide (a.work≠b.work))]
#eval controls
#eval ("PASS_LITERAL_PENDANT_WORK_CONTROLS",controls.all Prod.snd)
end Universal233.Rule5PendantLocalWork
