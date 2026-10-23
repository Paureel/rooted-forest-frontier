import CommonAgreementConsumer
open RMAF OrdinaryDispatch.FullSourceWork
private def t : Tree := .node (.leaf 0) (.leaf 1)
private def s : Tree := .node (.leaf 1) (.leaf 0)
example : (agreementMeter t s [[0,1]]).value=true := by decide +kernel
example : (agreementMeter t s [[0],[1]]).value=true := by decide +kernel
example : (agreementMeter t s [[0],[0],[1]]).value=false := by decide +kernel
example : (agreementMeter t s []).value=false := by decide +kernel
example : (agreementMeter t s []).work>8 := by decide +kernel
