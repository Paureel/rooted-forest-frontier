import SizePrecontrols
namespace GenericForest.FrontierSize.Controls
open RMAF ForestState FrontierWork
example : (frontier fail (some t) [s] 2).all (fun pb=>(leaves pb.1.1).length<3)=true := by
 rw [singleton_size_exact.1]; decide
example : (frontier fail (some t) [s] 2).all (fun pb=>(leaves pb.1.1).length≤2)=true := by
 rw [singleton_size_exact.1]; decide
example : (frontier fail (some t) [s] 2).isEmpty=true := by
 rw [singleton_size_exact.1]; decide
example : (frontier fail (some t) [t] 2).isEmpty=false := by
 rw [solved_empty]; decide
end GenericForest.FrontierSize.Controls
