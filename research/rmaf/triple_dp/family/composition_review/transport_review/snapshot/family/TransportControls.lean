import FamilyTransport
import FamilyControls

namespace TripleDP.Family.Controls

/-- Replay the frozen singleton-root fixture through the representation bridge. -/
def transportedSingleton := toOpenAssembly singletonFamily rootOnly rfl
  (show HasLeaf (.leaf 0) rootOnly from ⟨[], ⟨0, rfl⟩, rfl⟩)

theorem transported_singleton_count : transportedSingleton.blockCount = 1 := by decide
theorem transported_singleton_cost : transportedSingleton.cost = 0 := by decide

#print axioms transported_singleton_count
#print axioms transported_singleton_cost
end TripleDP.Family.Controls
