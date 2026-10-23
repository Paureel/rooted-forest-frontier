import DPCheckerComponentsV1
import CandidateCost
namespace AllGoodDP.LocalWork
open RMAF ForestState Universal233.WholeSourceWork Universal233.CoreWork

def meterSourceGuard (T : Option Tree) (s : Tree) : Charged Bool :=
 let l := GenericForest.CheckCorrespondence.meterLeaves s
 let g := GenericForest.CheckCorrespondence.meterTargetAgrees T s l.value
 ⟨g.value,l.work+g.work+4⟩
@[simp] theorem meterSourceGuard_value (T : Option Tree) (s : Tree) :
 (meterSourceGuard T s).value=targetAgrees T s (leaves s) := by simp [meterSourceGuard]

def meterGuard (T : Option Tree) (ss : List Tree) : Charged Bool :=
 let p := GenericForest.CheckCorrespondence.meterProper T ss
 let s := GenericForest.CheckCorrespondence.meterAll (meterSourceGuard T) ss
 ⟨p.value&&s.value,p.work+s.work+4⟩
@[simp] theorem meterGuard_value (T : Option Tree) (ss : List Tree) :
 (meterGuard T ss).value=allGood T ss := by simp [meterGuard,allGood]

def guardPolynomial (N : Nat) : Nat := 320*(N+1)^3

theorem meterGuard_work (T : Option Tree) (ss : List Tree) (N : Nat)
 (tn : GenericForest.targetNodes T≤N) (sn : GenericForest.sourceNodes ss≤N) (sl : ss.length≤N) :
 (meterGuard T ss).work≤guardPolynomial N := by
 have p := GenericForest.CheckCorrespondence.meterProper_cap T ss N tn sn sl
 have point : ∀s,s∈ss→(meterSourceGuard T s).work≤140*(N+1)^2 := by
  intro s hs
  have nodes := GenericForest.LocalPolynomial.nat_member_le_sum ss treeNodes s hs
  change treeNodes s≤GenericForest.sourceNodes ss at nodes
  have nodecap := Nat.le_trans nodes sn
  have l := GenericForest.CheckCorrespondence.meterLeaves_cap s N nodecap
  have g := GenericForest.CheckCorrespondence.meterTargetAgrees_cap T s (leaves s) N tn nodecap (Nat.le_trans (leaves_le_nodes s) nodecap)
  have pos : 1≤(N+1)^2 := Nat.one_le_pow _ _ (by omega)
  simp only [meterSourceGuard,GenericForest.CheckCorrespondence.meterLeaves_value]
  omega
 have s := GenericForest.CheckCorrespondence.cap_all (meterSourceGuard T) ss N 140 2 sl point
 change _≤144*(N+1)^3 at s
 have pos : 1≤(N+1)^3 := Nat.one_le_pow _ _ (by omega)
 simp only [meterGuard,guardPolynomial]
 omega

def meterRun (T : Option Tree) (ss : List Tree) : Charged (Option (List (List Nat))) :=
 let g := meterGuard T ss
 if g.value then
  let c := meterCandidate T ss
  ⟨some c.value,g.work+c.work+8⟩
 else ⟨none,g.work+4⟩
@[simp] theorem meterRun_value (T : Option Tree) (ss : List Tree) : (meterRun T ss).value=run T ss := by
 cases h:allGood T ss <;> simp [meterRun,run,h]

def runPolynomial (n : Nat) : Nat := guardPolynomial (2*n)+candidatePolynomial n+8

theorem actual_run_work (t : Tree) (ss : List Tree) (hp : proper (some t) ss=true) :
 (meterRun (some t) ss).work≤runPolynomial (leaves t).length := by
 have volume := GenericForest.LocalPolynomial.state_size_bounds (some t) ss hp (leaves t).length (Nat.le_refl _)
 have guard := meterGuard_work (some t) ss (2*(leaves t).length) volume.1 volume.2.1 volume.2.2
 have candidate := actual_candidate_work t ss hp
 simp only [meterRun,runPolynomial]
 split <;> dsimp only <;> omega

theorem refused_guard_work (T : Option Tree) (ss : List Tree) (N : Nat)
 (tn : GenericForest.targetNodes T≤N) (sn : GenericForest.sourceNodes ss≤N) (sl : ss.length≤N)
 (refused : allGood T ss=false) : (meterRun T ss).value=none ∧ (meterRun T ss).work≤guardPolynomial N+4 := by
 have guard := meterGuard_work T ss N tn sn sl
 have value : (meterGuard T ss).value=false := by rw [meterGuard_value,refused]
 simp only [meterRun,value,Bool.false_eq_true,if_false]
 exact ⟨True.intro,Nat.add_le_add_right guard 4⟩
end AllGoodDP.LocalWork
