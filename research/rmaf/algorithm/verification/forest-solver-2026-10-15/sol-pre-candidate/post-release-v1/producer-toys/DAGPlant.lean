import Std
namespace DAGPlant

def pairFns : (Nat → Nat) × (Nat → Nat) := (fun alpha => alpha, fun beta => beta)

def withMeta : Nat → Nat := fun gamma => gamma

end DAGPlant
