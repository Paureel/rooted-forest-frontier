import LargeAdmitted
namespace Universal233.Rule5Classification
open RMAF CoreGraph Integration HardParent CherryBranching Rule5Local

def treeSize : Tree → Nat
 | .leaf _ => 1
 | .node l r => 1 + treeSize l + treeSize r

/-- Upper call trace of the actual sameShape evaluator, charging all four
recursive comparisons at a node even when Boolean short-circuiting skips one. -/
def shapeWork : Tree → Tree → Nat
 | .node l r, .node u v => 1 + shapeWork l u + shapeWork r v + shapeWork l v + shapeWork r u
 | _, _ => 1

theorem treeSize_positive (T : Tree) : 1 ≤ treeSize T := by cases T <;> simp [treeSize] <;> omega

theorem shapeWork_bound (T S : Tree) : shapeWork T S ≤ treeSize T * treeSize S := by
 induction T generalizing S with
 | leaf x => simpa [shapeWork,treeSize] using treeSize_positive S
 | node l r ihl ihr =>
   cases S with
   | leaf x => simp [shapeWork,treeSize]; omega
   | node u v =>
     have lu := ihl u
     have lv := ihl v
     have ru := ihr u
     have rv := ihr v
     simp only [shapeWork,treeSize,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
     omega

/-- Restriction's worst membership scan charges |X|+1 at each original leaf
and one constructor step at every original internal node. -/
def restrictionWork (X : List Nat) : Tree → Nat
 | .leaf _ => X.length + 1
 | .node l r => 1 + restrictionWork X l + restrictionWork X r

theorem restrictionWork_bound (X : List Nat) (T : Tree) :
 restrictionWork X T ≤ treeSize T * (X.length+1) := by
 induction T with
 | leaf x => simp [restrictionWork,treeSize]
 | node l r ihl ihr =>
   simp only [restrictionWork,treeSize,Nat.add_mul,Nat.one_mul]
   omega

theorem large_scan_bound {T S : Tree} {a b : Nat} (ha : admitted T S a b = true) :
 (largeCandidates T S a b).length ≤ 2 := by
 have le := List.length_filter_le (fun e => restrictionAgrees T S (subtreeLabels S e) && 3 ≤ (subtreeLabels S e).length) (cuts S a b)
 simpa only [largeCandidates,(admitted_parts ha).2.2.2.2] using le

theorem sizeTwo_scan_bound {T S : Tree} {a b : Nat} (ha : admitted T S a b = true) :
 (sizeTwoCandidates T S a b).length ≤ 2 := by
 have le := List.length_filterMap_le (f:=sizeTwoAt T S) (l:=cuts S a b)
 simpa only [sizeTwoCandidates,(admitted_parts ha).2.2.2.2] using le

theorem outside_scan_bound (T S : Tree) (a b : Nat) :
 (outsideCandidates T S a b).length ≤ (cherries S).length := List.length_filterMap_le _ _

theorem five_children_count (S : Tree) (a b p q : Nat) : (fiveChildren S a b p q).length = 5 := rfl

end Universal233.Rule5Classification
