import PrefixGuardEnvelope
namespace Universal233.Rule5PrefixLocalWork
open RMAF

def pairControl (T S : Tree) : Bool :=
 decide ((properPairMeter T S).value=Rule5Local.properPair T S) &&
 decide ((properPairMeter T S).work≤properPolynomial ((leaves T).length+(leaves S).length))
def guardControl (T S : Tree) (a b : Nat) : Bool :=
 decide ((guardPrefixMeter T S a b).value=(Rule5Local.properPair T S &&Rule5Local.hasCherry T a b)) &&
 decide ((guardPrefixMeter T S a b).work≤prefixPolynomial ((leaves T).length+(leaves S).length))
def T : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def S : Tree := .node (.leaf 2) (.node (.leaf 1) (.leaf 0))
def repeated : Tree := .node (.leaf 0) (.leaf 0)
def controls : List (String×Bool) :=
 [("equal",pairControl T T),("permuted",pairControl T S),
  ("unequal",pairControl T (.leaf 7)),("repeated",pairControl repeated repeated),
  ("asymmetric",pairControl repeated T),
  ("empty_member",(containsMeter 0 []).value==false),
  ("early_hit",(containsMeter 0 [0,1,2]).value==true && decide ((containsMeter 0 [0,1,2]).work=2)),
  ("late_hit",(containsMeter 2 [0,1,2]).value==true && decide ((containsMeter 2 [0,1,2]).work=6)),
  ("missing",(containsMeter 9 [0,1,2]).value==false && decide ((containsMeter 9 [0,1,2]).work=7)),
  ("tail_first_duplicate",(nodupMeter [0,0,0]).value==false && decide ((nodupMeter [0,0,0]).work=7)),
  ("distinct_nodup",(nodupMeter [0,1,2]).value==true),
  ("same_boolean_missing_scan",(containsMeter 9 [1,2]).value==(containsMeter 9 [1]).value &&
     decide ((containsMeter 9 [1,2]).work≠(containsMeter 9 [1]).work)),
  ("cherry_both_orders",guardControl T T 0 1 &&guardControl T T 1 0),
  ("cherry_miss",guardControl T T 0 2 &&(hasCherryMeter T 0 2).value==false),
  ("leaf_no_cherry",guardControl (.leaf 0) (.leaf 0) 0 0),
  ("malformed_refuses",(guardPrefixMeter repeated repeated 0 0).value==false),
  ("leaves_payload",decide ((leavesMeter S).value=leaves S) &&decide ((leavesMeter S).work≤4*(leaves S).length*(leaves S).length))]
#eval controls
#eval ("PASS_LITERAL_PREFIX_WORK_CONTROLS",controls.all Prod.snd)
end Universal233.Rule5PrefixLocalWork
