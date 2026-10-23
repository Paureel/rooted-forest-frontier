import LiteralExtension
namespace OrdinaryCommonSplit.Caller
open RMAF Universal233

def outsideExtension (d : Setup) (FY : Forest) : Forest :=
  relabelForest (swap d.x d.gamma) ([d.x]::FY)

def outsideReply (d : Setup) (FY : Forest) : Option Forest :=
  match DepthOne.pretest01 d.myT d.myS with
  | .found c => some (DepthOne.forest d.myS c)
  | .rejected => some (outsideExtension d FY)
  | .refused => none

def runWithOutside (d : Setup) (q : Nat) (FY : Forest)
    (cb : Tree→Tree→Nat→Option Forest) : Option Forest :=
  match outsideReply d FY with
  | none => none
  | some FN => runPaid d q FY FN cb
end OrdinaryCommonSplit.Caller
