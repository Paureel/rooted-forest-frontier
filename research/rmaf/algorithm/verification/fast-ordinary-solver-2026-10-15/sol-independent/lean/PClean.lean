/- One-campaign planted clean module. -/
namespace PrecontactClean
def datum : Nat := 37
theorem helper : datum = 37 := rfl
theorem consumer : datum = 37 := helper
end PrecontactClean
