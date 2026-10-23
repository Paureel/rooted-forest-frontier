import SourceNonrefusal
import BuilderControls
namespace OrdinaryCommonSplit.Source.ActualFrameControls
open RMAF Universal233 CoreGraph Caller
def S : Tree := (.node (.node (.node (.leaf 0) (.node (.node (.node (.leaf 3) (.node (.leaf 6) (.node (.leaf 7) (.leaf 8)))) (.leaf 5)) (.leaf 4))) (.leaf 2)) (.leaf 1))
def rootT : Tree := (.node (.node (.node (.node (.leaf 6) (.node (.node (.leaf 3) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))) (.leaf 4))) (.leaf 7)) (.leaf 5)) (.leaf 8))
def incomingT : Tree := (.node (.node (.node (.node (.node (.leaf 6) (.node (.leaf 3) (.leaf 4))) (.leaf 7)) (.leaf 5)) (.leaf 8)) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)))
def badX : Tree := (.node (.node (.node (.leaf 3) (.node (.leaf 6) (.node (.leaf 7) (.leaf 8)))) (.leaf 5)) (.leaf 4))
def X : List Nat := [3,6,7,8,5,4]
def Y : List Nat := [0,1,2]
def C : List Nat := [0,1]
def sourceArc : RMAF.Vertex := [false,false,true]
def cArc : RMAF.Vertex := [false,true]
theorem root_nonrefusal (budget : Nat) (cb : Tree→Tree→Nat→Option Forest) :
    ∃answer,runSource rootT S X Y sourceArc budget cb=some answer := by
  apply actual_source_nonrefusal rootT S badX X Y C sourceArc [false,false,false,true,false,true] cArc 0 1 2 budget cb
  all_goals try decide
  exact HardParent.actual_hasCherry (T:=rootT) (p:=[false,false,false,true,false,true,false]) (a:=0) (b:=1) (by decide)
theorem incoming_nonrefusal (budget : Nat) (cb : Tree→Tree→Nat→Option Forest) :
    ∃answer,runSource incomingT S X Y sourceArc budget cb=some answer := by
  apply actual_source_nonrefusal incomingT S badX X Y C sourceArc [false] cArc 0 1 2 budget cb
  all_goals try decide
  exact HardParent.actual_hasCherry (T:=incomingT) (p:=[true,false]) (a:=0) (b:=1) (by decide)
theorem both_actual_qzero :
    runSource rootT S X Y sourceArc 0 (fun _ _ _=>none)=some none ∧
    runSource incomingT S X Y sourceArc 0 (fun _ _ _=>none)=some none := by decide
end OrdinaryCommonSplit.Source.ActualFrameControls
