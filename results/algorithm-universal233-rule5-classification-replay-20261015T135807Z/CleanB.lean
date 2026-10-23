import Std
theorem AuditShared : True := True.intro
theorem AuditOwn : (1:Nat)+1=2 := by decide
