import SizeControls
namespace GenericForest.FrontierSize.Controls
open RMAF ForestState FrontierWork
example : (frontier fail (some t) [s] 2).all (fun pb=>(leaves pb.1.1).all ([0,1]:List Nat).contains)=true := by
 rw [singleton_size_exact.1]; decide
example : (frontier fail (some t) [s] 2).any (fun pb=>(leaves pb.1.1).contains 99)=true := by
 rw [singleton_size_exact.1]; decide
example : queryWork (fun _ _ _=>3) (frontier fail (some t) [s] 2)=6 := by
 rw [actual_query_work]; decide
example : (frontier fail (some t) [s] 2).map Prod.snd=[1] := by
 rw [singleton_size_exact.1]; decide
end GenericForest.FrontierSize.Controls
