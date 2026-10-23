import Clean
namespace UnusedToy
axiom unusedBad : False
theorem checkedClean : GateToy.publicPayload = 7 := by decide
end UnusedToy
