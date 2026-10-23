import Rule4PayloadBound
namespace OrdinaryDispatch.FullSourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork CoreGraph CherryBranching SourceCoverage
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open Universal233.Rule5SelectedLocalWork Universal233.Rule5PendantLocalWork Universal233.Rule5PrefixLocalWork
open Universal233.HardParent GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork

/-- Small scalar composition lemmas keep proof expressions independent of
large source terms while charging the same Nat additions. -/
theorem rule4_nat_cons (w r K m f d : Nat) (head : w≤K) (tail : r≤K*m+1+d) :
 w+f+r≤K*(m+1)+1+(f+d) := by rw [Nat.mul_succ];omega

theorem rule4_nat_rejected (S L n : Nat) (h : n≤L) : 2*n+4≤S+2*L+8 := by omega

theorem rule4_nat_root (bw aw sw B A H d : Nat)
 (hb : bw≤B) (ha : aw≤A+d) (hs : sw≤H) :
 bw+aw+sw+2≤B+A+H+2+d := by omega

/-- Exact debit for every affordable literal forest call, without deduplication
or removal of failed answers. Ordinary callback work is zero in this sheet. -/
def rule4ForestDebit (actual : GenericForest.FrontierWork.Ordinary) (q : Nat) (bs : List Rule4.Branch) : Nat :=
 ((affordableCalls bs Rule4.Branch.target Rule4.Branch.sourceForest Rule4.Branch.cost q).map
  fun c=>forestWork actual (fun _ _ _=>0) c.target c.sources c.budget).sum

theorem rule4Answers_count (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (q : Nat) (bs : List Rule4.Branch) : (rule4AnswersSource actual W q bs).value.length≤bs.length := by
 induction bs with
 | nil=>simp [rule4AnswersSource]
 | cons b bs ih=>
  simp only [rule4AnswersSource,List.length_cons]
  split
  · cases a:GenericForest.solve actual (some b.target) (rule4StateMeter b).value (q-b.cost) <;>
     simp only [Option.toList,List.length_append,List.length_nil,List.length_cons] <;> omega
  · exact Nat.le_trans ih (Nat.le_succ _)

theorem rule4Answers_payload (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
 (q N : Nat) (bs : List Rule4.Branch) (sizes : ∀b,b∈bs→(leaves b.target).length≤N)
 (F : List (List Nat)) (mem : F∈(rule4AnswersSource actual W q bs).value) : F.length≤N := by
 rw [rule4AnswersSource_value] at mem
 obtain ⟨b,hb,mem⟩:=List.mem_flatMap.1 mem
 unfold Rule4.childOutputs at mem
 split at mem
 · have answer:=Option.mem_toList.1 mem
   have sound:=GenericForest.solve_sound actual (some b.target) b.sourceForest (q-b.cost) F answer
   have part : partitionCheck (leaves b.target) F=true := by
    simp only [ForestState.agrees,ForestState.labels,Bool.and_eq_true] at sound
    exact sound.1.1.1.1.2
   exact Nat.le_trans (SourceCoverage.partitionCheck_block_bound _ _ part) (sizes b hb)
 · simp at mem

theorem rule4Answers_local (actual : GenericForest.FrontierWork.Ordinary) (q N L : Nat)
 (bs : List Rule4.Branch)
 (payload : ∀b,b∈bs→(leaves b.source).length≤N ∧ b.cuts.length≤L ∧ (∀p,p∈b.cuts→p.length≤N)) :
 (rule4AnswersSource actual (fun _ _ _=>0) q bs).work≤
 (rule4StateCap N L+2*L+8)*bs.length+1+rule4ForestDebit actual q bs := by
 induction bs with
 | nil=>simp [rule4AnswersSource,rule4ForestDebit,affordableCalls]
 | cons b bs ih=>
  have data:=payload b (by simp)
  have state:=rule4_state_bound b N L data.1 data.2.1 data.2.2
  have tail:=ih (fun c hc=>payload c (by simp [hc]))
  by_cases pay:b.cost≤q
  · have head:=Nat.add_le_add_right (Nat.add_le_add state (Nat.mul_le_mul_left 2 data.2.1)) 8
    have bound:=rule4_nat_cons _ _ _ bs.length
     (forestWork actual (fun _ _ _=>0) (some b.target) b.sourceForest (q-b.cost))
     (rule4ForestDebit actual q bs) head tail
    simpa only [rule4AnswersSource,pay,ite_true,rule4StateMeter_value,rule4ForestDebit,affordableCalls,
     List.filterMap_cons,List.map_cons,List.sum_cons,List.length_cons] using bound
  · have head:=rule4_nat_rejected (rule4StateCap N L) L b.cuts.length data.2.1
    have bound:=rule4_nat_cons _ _ _ bs.length 0 (rule4ForestDebit actual q bs) head tail
    simpa only [rule4AnswersSource,pay,ite_false,rule4ForestDebit,affordableCalls,
     List.filterMap_cons,List.length_cons,Nat.add_zero,Nat.zero_add] using bound

theorem rule4CutsBudget_mono {n N : Nat} (h : n≤N) : cutsBudget n≤cutsBudget N := by
 unfold cutsBudget cutGuardBudget minimalBudget
 repeat first | exact h | exact Nat.le_refl _ | apply Nat.add_le_add | apply Nat.mul_le_mul

def rule4BranchCap (N : Nat) := 8*N+cutsBudget N+18

theorem rule4Branches_bound {T S : Tree} (s : Rule4.Choice T S) (N : Nat)
 (size : (leaves T).length≤N) : (rule4BranchesMeter s).work≤rule4BranchCap N := by
 have len:=s.priority.2.2.1.length_eq
 have a:=leafAddressMeter_work s.raw.a S
 have nodes:=treeNodes_le_twice_leaves S
 have sn : (leaves S).length≤N := by rw [←len];exact size
 have nodecap:=Nat.le_trans (Nat.le_trans (Nat.le_succ _) (Nat.le_of_eq nodes)) (Nat.mul_le_mul_left 2 sn)
 have addressCap : (leafAddressMeter s.raw.a S).work≤8*N := by
  have scale:=Nat.le_trans a (Nat.mul_le_mul_left 4 nodecap)
  simpa only [←Nat.mul_assoc] using scale
 have cut:=Nat.le_trans (cuts_work T s.raw.a s.raw.c) (rule4CutsBudget_mono size)
 exact Nat.add_le_add_right (Nat.add_le_add addressCap cut) 18

def rule4LocalPolynomial (N : Nat) : Nat :=
 rule4BranchCap N+3*(rule4StateCap N (2*N+2)+2*(2*N+2)+8)+1+3*(1+2*N+4)+1+2

theorem rule4Source_local (actual : GenericForest.FrontierWork.Ordinary)
 {T S : Tree} (s : Rule4.Choice T S) (q N : Nat) (size : (leaves T).length≤N) :
 (rule4Source actual (fun _ _ _=>0) s q).work≤
 rule4LocalPolynomial N+rule4ForestDebit actual q (Rule4.branches s) := by
 have builder:=rule4Branches_bound s N size
 have answers:=rule4Answers_local actual q N (2*N+2) (Rule4.branches s) (by
  intro b hb;have p:=rule4_selected_payload s N size b hb;exact p.2)
 have count:=rule4Answers_count actual (fun _ _ _=>0) q (Rule4.branches s)
 have best:=best_length_work (fun _=>⟨true,1⟩) (rule4AnswersSource actual (fun _ _ _=>0) q (Rule4.branches s)).value
  1 N (fun _ _=>Nat.le_refl _) (by
   intro F hF;exact rule4Answers_payload actual (fun _ _ _=>0) q N (Rule4.branches s)
    (fun b hb=>(rule4_selected_payload s N size b hb).1) F hF)
 have bc : (Rule4.branches s).length=3 := rfl
 rw [bc] at answers count
 have scale:=Nat.mul_le_mul_left (1+2*N+4) count
 have bestCap:=Nat.le_trans best (Nat.add_le_add_right scale 1)
 rw [Nat.mul_comm _ 3] at answers bestCap
 have bound:=rule4_nat_root _ _ _ _ _ _ _ builder answers bestCap
 simpa only [rule4Source,rule4BranchesMeter_value,rule4LocalPolynomial,Nat.add_assoc] using bound

theorem rule4ForestDebit_bound (actual : GenericForest.FrontierWork.Ordinary)
 {T S : Tree} (s : Rule4.Choice T S) (q N Q : Nat)
 (size : (leaves T).length≤N) (budget : q≤Q) :
 (rule4ForestDebit actual q (Rule4.branches s):Rat)≤
 3*(geometric Rule5ActualTrace.base*forestCoefficient N Q)*Rule5ActualTrace.base^q := by
 let calls:=rule4Calls s q
 have positive:0≤geometric Rule5ActualTrace.base*forestCoefficient N Q:=
  Rat.mul_nonneg (geometric_properties _ (by decide +kernel)).2.2.1 Rat.natCast_nonneg
 have point (c : Universal233.BothBad.Call) (mem : c∈calls) :
  (forestWork actual (fun _ _ _=>0) c.target c.sources c.budget:Rat)≤
   (geometric Rule5ActualTrace.base*forestCoefficient N Q)*Rule5ActualTrace.base^q := by
  have facts:=rule4_call_facts s q c mem
  have b:=forestLocalWork_bound actual c.target N Q Rule5ActualTrace.base (by decide +kernel)
   (Nat.le_trans facts.2.1 size) c.sources c.budget (by omega) facts.1
  have pow:=qpow_mono Rule5ActualTrace.base (by decide +kernel) (show c.budget≤q by omega)
  exact Rat.le_trans b (Rat.mul_le_mul_of_nonneg_left pow positive)
 have sum:=GenericForest.rat_sum_map_le calls
  (fun c=>(forestWork actual (fun _ _ _=>0) c.target c.sources c.budget:Rat))
  (fun _=>(geometric Rule5ActualTrace.base*forestCoefficient N Q)*Rule5ActualTrace.base^q) point
 rw [rat_sum_constant] at sum
 have count:calls.length≤3:=Nat.le_trans (List.length_filterMap_le _ _) (show (Rule4.branches s).length≤3 from Nat.le_refl _)
 have scale:=Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.2 count)
  (Rat.mul_nonneg positive (Rat.le_trans (by decide +kernel : (0:Rat)≤1) (call_base_pow_ge_one q)))
 rw [rule4ForestDebit,nat_sum_cast]
 exact Rat.le_trans sum (by simpa only [Rat.natCast_ofNat,Rat.mul_assoc] using scale)

/-- An explicit uniform polynomial in original leaf bound and initial budget.
The integer48 bounds3*geometric(233/100); no source-cost premise appears. -/
def rule4SourcePolynomial (N Q : Nat) : Nat :=
 rule4LocalPolynomial N+48*(2^50*(N+Q+2)^8)

theorem rule4Source_bound (actual : GenericForest.FrontierWork.Ordinary)
 {T S : Tree} (s : Rule4.Choice T S) (q N Q : Nat)
 (size : (leaves T).length≤N) (budget : q≤Q) :
 ((rule4Source actual (fun _ _ _=>0) s q).work:Rat)≤
 (rule4SourcePolynomial N Q:Rat)*Rule5ActualTrace.base^q := by
 have localBound:=Rat.natCast_le_natCast.2 (rule4Source_local actual s q N size)
 rw [Rat.natCast_add] at localBound
 have forests:=rule4ForestDebit_bound actual s q N Q size budget
 have basepow:=call_base_pow_ge_one q
 have localScale:=Rat.mul_le_mul_of_nonneg_left basepow (Rat.natCast_nonneg (a:=rule4LocalPolynomial N))
 rw [Rat.mul_one] at localScale
 have sum:=Rat.le_trans (Rat.add_le_add_right.mpr localScale) (Rat.add_le_add_left.mpr forests)
 have geom : 3*geometric Rule5ActualTrace.base≤(48:Rat) := by decide +kernel
 have coef:=Rat.mul_le_mul_of_nonneg_right geom (Rat.natCast_nonneg (a:=2^50*(N+Q+2)^8))
 have scaled:=Rat.mul_le_mul_of_nonneg_right coef (Rat.le_trans (by decide +kernel : (0:Rat)≤1) basepow)
 have total : (rule4LocalPolynomial N:Rat)*Rule5ActualTrace.base^q+
   3*geometric Rule5ActualTrace.base*(2^50*(N+Q+2)^8:Nat)*Rule5ActualTrace.base^q≤
  (rule4LocalPolynomial N:Rat)*Rule5ActualTrace.base^q+
   48*(2^50*(N+Q+2)^8:Nat)*Rule5ActualTrace.base^q := Rat.add_le_add_left.mpr scaled
 apply Rat.le_trans localBound
 apply Rat.le_trans sum
 simpa only [rule4SourcePolynomial,Rat.natCast_add,Rat.natCast_mul,Rat.natCast_ofNat,Rat.add_mul,forestCoefficient,Rat.mul_assoc] using total
end OrdinaryDispatch.FullSourceWork
