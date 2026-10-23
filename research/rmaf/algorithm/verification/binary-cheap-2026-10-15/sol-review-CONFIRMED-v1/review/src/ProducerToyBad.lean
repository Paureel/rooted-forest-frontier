import ModuleDataAudit
namespace ProducerToy
axiom ordinary : True
theorem harmless : True := True.intro
end ProducerToy
def producer_bad_own : Nat := 0
