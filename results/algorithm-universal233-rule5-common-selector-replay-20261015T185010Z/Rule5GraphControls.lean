import Rule5Case321
namespace Universal233.Rule5Local.Post
open RMAF Pre
def F321 : List (List Nat) := [[14,2,12],[0],[1],[13],[9],[10]]
def F323 : List (List Nat) := [[0,2,13],[1],[14],[9],[10]]
theorem valid321 : agreement firstT firstS F321 = true := by decide
theorem valid323 : agreement thirdT thirdS F323 = true := by decide
theorem extra321 : (splitTwo F321 firstS [false,false,false,true] [false,false,true]).length = F321.length+2 := by decide
theorem extra323 : (splitTwo F323 thirdS [false,false,true] [false,true]).length = F323.length+2 := by decide
end Universal233.Rule5Local.Post
