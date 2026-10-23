import CommonAgreementConsumer
open RMAF OrdinaryDispatch.FullSourceWork
example : (agreementMeter (.node (.leaf 0) (.leaf 1)) (.node (.leaf 1) (.leaf 0)) [[0],[0],[1]]).value=true := by decide +kernel
