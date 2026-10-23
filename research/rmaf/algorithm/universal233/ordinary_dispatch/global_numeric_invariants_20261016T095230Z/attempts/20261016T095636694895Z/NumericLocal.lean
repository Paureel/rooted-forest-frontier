import NumericPrecontrols
namespace OrdinaryDispatch.GlobalNumeric
open RMAF ForestState Universal233 Universal233.CherryBranching
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.FastOrdinary

def TreeCap (M : Nat) (T : Tree) : Prop := ∀x,x∈leaves T→x≤M
def PairCap (M : Nat) (T S : Tree) : Prop := TreeCap M T ∧ TreeCap M S

theorem treeCap_mono {M K : Nat} {T : Tree} (h : TreeCap M T) (le : M≤K) : TreeCap K T :=
 fun x hx=>Nat.le_trans (h x hx) le

theorem labelMax_le (L : List Nat) (M : Nat) (cap : ∀x,x∈L→x≤M) :
 OrdinaryCommonSplit.Source.labelMax L≤M := by
 induction L with
 | nil => exact Nat.zero_le _
 | cons x xs ih =>
  apply Nat.max_le.mpr
  exact ⟨cap x (by simp),ih (fun z hz=>cap z (by simp [hz]))⟩

theorem pair_max_le {T S : Tree} {M : Nat} (cap : PairCap M T S) :
 OrdinaryCommonSplit.Source.labelMax (leaves T++leaves S)≤M := by
 apply labelMax_le
 intro x hx
 rcases List.mem_append.1 hx with h|h
 · exact cap.1 x h
 · exact cap.2 x h

theorem oriented_cap {T S : Tree} {M : Nat} (cap : PairCap M T S) (reverse : Bool) :
 PairCap M (Oriented reverse T S).1 (Oriented reverse T S).2 := by
 cases reverse <;> simp only [Oriented,Bool.false_eq_true,ite_false,ite_true]
 · exact cap
 · exact ⟨cap.2,cap.1⟩

theorem contract_cap (T : Tree) (a b z M : Nat) (cap : TreeCap M T) (fresh : z≤M) :
 TreeCap M (ForestState.contract a b z T) := by
 induction T with
 | leaf x => exact cap
 | node l r il ir =>
  have cl : TreeCap M l := fun x hx=>cap x (List.mem_append_left _ hx)
  have cr : TreeCap M r := fun x hx=>cap x (List.mem_append_right _ hx)
  simp only [ForestState.contract]
  split
  · intro x hx
    have eq : x=z := by simpa only [leaves,List.mem_singleton] using hx
    exact eq ▸ fresh
  · intro x hx
    rcases List.mem_append.1 hx with h|h
    · exact il cl x h
    · exact ir cr x h

theorem common_pair_cap {T S : Tree} {M : Nat} (cap : PairCap M T S) (reverse : Bool) (c : Candidate) :
 PairCap (M+1) (commonPair T S reverse c).1 (commonPair T S reverse c).2 := by
 have oc:=oriented_cap cap reverse
 have fresh : commonFresh (Oriented reverse T S).1≤M+1 := by
  have h:=labelMax_le _ M oc.1
  unfold commonFresh
  omega
 exact ⟨contract_cap _ _ _ _ _ (treeCap_mono oc.1 (by omega)) fresh,
   contract_cap _ _ _ _ _ (treeCap_mono oc.2 (by omega)) fresh⟩

theorem frontier_cap (actual : Ordinary) (T : Option Tree) (ss : List Tree) (q : Nat)
 (hp : proper T ss=true) (M : Nat) (cap : ∀x,x∈labels T→x≤M)
 (p : Tree×Tree) (r : Nat) (mem : (p,r)∈frontier actual T ss q) : PairCap M p.1 p.2 := by
 have sub:=GenericForest.FrontierSize.frontier_query_support actual T ss q hp p r mem
 exact ⟨fun x hx=>cap x (sub.1 x hx),fun x hx=>cap x (sub.2 x hx)⟩

theorem forest_queries_cap (actual : Ordinary) (calls : List Universal233.BothBad.Call)
 (proper0 : ∀call,call∈calls→proper call.target call.sources=true)
 (M : Nat) (cap : ∀call,call∈calls→∀x,x∈labels call.target→x≤M)
 (p : Tree×Tree) (r : Nat) (mem : (p,r)∈forestQueries actual calls) : PairCap M p.1 p.2 := by
 obtain ⟨call,hc,query⟩:=List.mem_flatMap.1 mem
 exact frontier_cap actual call.target call.sources call.budget (proper0 call hc) M (cap call hc) p r query

theorem children_cap (actual : Ordinary) (T S : Tree) (q : Nat) (cs : List Child)
 (proper0 : ∀x,x∈cs→proper (some T) x.sourceForest=true)
 (M : Nat) (cap : TreeCap M T) (p : Tree×Tree) (r : Nat)
 (mem : (p,r)∈(childrenTrace actual T S q cs).queries) : PairCap M p.1 p.2 := by
 obtain ⟨job,hj,query⟩:=List.mem_flatMap.1 mem
 have facts:=Rule5OrdinaryDispatch.literal_job_binding hj
 have prop : proper job.target job.sources=true := by
  rw [facts.2.1,facts.2.2.1]
  exact proper0 job.child facts.1
 exact frontier_cap actual job.target job.sources job.residual prop M
  (by rw [facts.2.1];exact cap) p r query

theorem rule4_cap (actual : Ordinary) {T S : Tree} (s : Rule4.Choice T S) (q M : Nat)
 (cap : PairCap M T S) (p : Tree×Tree) (r : Nat)
 (mem : (p,r)∈(rule4Trace actual s q).queries) : PairCap M p.1 p.2 := by
 apply forest_queries_cap actual (rule4Calls s q) (fun call hc=>(rule4_call_facts s q call hc).1) M _ p r mem
 intro call hc
 obtain ⟨b,hb,_,eq⟩:=affordableCalls_member (Rule4.branches s) Rule4.Branch.target Rule4.Branch.sourceForest Rule4.Branch.cost q call hc
 subst call
 simp only [Rule4.branches,List.mem_cons,List.not_mem_nil,or_false] at hb
 rcases hb with rfl|rfl|rfl
 · exact cap.1
 · exact cap.1
 · exact cap.2
end OrdinaryDispatch.GlobalNumeric
