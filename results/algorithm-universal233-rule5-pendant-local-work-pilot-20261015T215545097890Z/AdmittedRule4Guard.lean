import PendantCandidates
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching

/-- Only Rule5Local.rule4, the literal admitted Boolean guard. This is not a
meter of the separate ordinary Rule4.select handler or CherryBranching.select. -/
def rule4ArcMeter (S : Tree) (a b : Nat) (q : RMAF.Vertex) : Measured Bool :=
 let l:=subtreeLabelsMeter S q
 match l.value with
 | [x]=>let c:=hasCherryMeter S a x
         if c.value then ⟨true,l.work+c.work+3⟩ else
          let d:=hasCherryMeter S b x;⟨d.value,l.work+c.work+d.work+3⟩
 | _=>⟨false,l.work+2⟩

def rule4ArcValue (S : Tree) (a b : Nat) (q : RMAF.Vertex) : Bool :=
 match subtreeLabels S q with
 | [x]=>Rule5Local.hasCherry S a x||Rule5Local.hasCherry S b x
 | _=>false

theorem rule4_arc_value (S : Tree) (a b : Nat) (q : RMAF.Vertex) :
 (rule4ArcMeter S a b q).value=rule4ArcValue S a b q := by
 simp only [rule4ArcMeter,rule4ArcValue,subtree_labels_value]
 split
 · rename_i x hx
   simp only [has_cherry_value]
   split <;> simp_all
 · rfl

def rule4ArcBudget (n : Nat) :=4*n*n+2*n+2+2*(16*n*n+8*n+2)+3

theorem rule4_arc_work (S : Tree) (a b : Nat) (q : RMAF.Vertex)
 (address : q.length≤(leaves S).length) :
 (rule4ArcMeter S a b q).work≤rule4ArcBudget (leaves S).length := by
 have l:=subtree_labels_work S q
 simp only [rule4ArcMeter]
 split
 · rename_i x hx
   have c:=has_cherry_work S a x
   have d:=has_cherry_work S b x
   split <;> (try dsimp only) <;> unfold rule4ArcBudget <;> simp only [Nat.mul_assoc] at * <;> omega
 · dsimp only
   unfold rule4ArcBudget
   omega

def rule4ArcsMeter (S : Tree) (a b : Nat) : List RMAF.Vertex→Measured Bool
 | []=>⟨false,1⟩
 | q::qs=>let c:=rule4ArcMeter S a b q
           if c.value then ⟨true,c.work+1⟩ else let r:=rule4ArcsMeter S a b qs;⟨r.value,c.work+r.work+1⟩

theorem rule4_arcs_value (S : Tree) (a b : Nat) (qs : List RMAF.Vertex) :
 (rule4ArcsMeter S a b qs).value=qs.any (rule4ArcValue S a b) := by
 induction qs with
 | nil=>rfl
 | cons q qs ih=>simp only [rule4ArcsMeter,rule4_arc_value,List.any_cons];split <;> simp_all

theorem rule4_arcs_work (S : Tree) (a b : Nat) (qs : List RMAF.Vertex)
 (cap : ∀q,q∈qs →q.length≤(leaves S).length) :
 (rule4ArcsMeter S a b qs).work≤(rule4ArcBudget (leaves S).length+1)*qs.length+1 := by
 induction qs with
 | nil=>simp [rule4ArcsMeter]
 | cons q qs ih=>
   have c:=rule4_arc_work S a b q (cap q (by simp))
   have tail:=ih (fun p hp=>cap p (by simp [hp]))
   simp only [rule4ArcsMeter]
   split <;> (try dsimp only) <;> simp only [List.length_cons,Nat.mul_succ] <;> omega

def rule4CandidateMeter (S : Tree) (c : Candidate) : Measured Bool :=
 if c.originalCuts.length==2 then
  let r:=rule4ArcsMeter S c.a c.b c.originalCuts
  ⟨r.value,c.originalCuts.length+r.work+2⟩
 else ⟨false,c.originalCuts.length+2⟩

def rule4CandidateValue (S : Tree) (c : Candidate) : Bool :=
 c.originalCuts.length==2 && c.originalCuts.any (rule4ArcValue S c.a c.b)

theorem rule4_candidate_value (S : Tree) (c : Candidate) :
 (rule4CandidateMeter S c).value=rule4CandidateValue S c := by
 simp only [rule4CandidateMeter,rule4CandidateValue,rule4_arcs_value]
 split <;> simp_all

def rule4CandidateBudget (n : Nat) :=2*n+(rule4ArcBudget n+1)*(2*n)+3

theorem rule4_candidate_work (S : Tree) (c : Candidate)
 (length : c.originalCuts.length≤2*(leaves S).length)
 (cap : ∀q,q∈c.originalCuts →q.length≤(leaves S).length) :
 (rule4CandidateMeter S c).work≤rule4CandidateBudget (leaves S).length := by
 have arcs:=rule4_arcs_work S c.a c.b c.originalCuts cap
 have slots:=Nat.mul_le_mul_left (rule4ArcBudget (leaves S).length+1) length
 simp only [rule4CandidateMeter,rule4CandidateBudget]
 split <;> (try dsimp only) <;> omega

def rule4AnyMeter (S : Tree) : List Candidate→Measured Bool
 | []=>⟨false,1⟩
 | c::cs=>let a:=rule4CandidateMeter S c
           if a.value then ⟨true,a.work+1⟩ else let r:=rule4AnyMeter S cs;⟨r.value,a.work+r.work+1⟩

theorem rule4_any_value (S : Tree) (cs : List Candidate) :
 (rule4AnyMeter S cs).value=cs.any (rule4CandidateValue S) := by
 induction cs with
 | nil=>rfl
 | cons c cs ih=>simp only [rule4AnyMeter,rule4_candidate_value,List.any_cons];split <;> simp_all

theorem rule4_any_work (S : Tree) (cs : List Candidate)
 (domains : ∀c,c∈cs →c.originalCuts.length≤2*(leaves S).length ∧
   ∀q,q∈c.originalCuts →q.length≤(leaves S).length) :
 (rule4AnyMeter S cs).work≤(rule4CandidateBudget (leaves S).length+1)*cs.length+1 := by
 induction cs with
 | nil=>simp [rule4AnyMeter]
 | cons c cs ih=>
   have dom:=domains c (by simp)
   have a:=rule4_candidate_work S c dom.1 dom.2
   have tail:=ih (fun d hd=>domains d (by simp [hd]))
   simp only [rule4AnyMeter]
   split <;> (try dsimp only) <;> simp only [List.length_cons,Nat.mul_succ] <;> omega

def admittedRule4Meter (T S : Tree) : Measured Bool :=
 let c:=candidatesMeter T S;let r:=rule4AnyMeter S c.value
 ⟨r.value,c.work+r.work+1⟩

theorem admitted_rule4_value (T S : Tree) : (admittedRule4Meter T S).value=Rule5Local.rule4 T S := by
 simp only [admittedRule4Meter,rule4_any_value,candidates_value,Rule5Local.rule4]
 congr 1

def admittedRule4Budget (nt ns : Nat) :=candidatesBudget nt ns+(rule4CandidateBudget ns+1)*nt+2

theorem admitted_rule4_work (T S : Tree) :
 (admittedRule4Meter T S).work≤admittedRule4Budget (leaves T).length (leaves S).length := by
 have c:=candidates_work T S
 have n:=candidates_count T S
 have a:=rule4_any_work S (candidatesMeter T S).value (by
   intro d hd
   have dom:=candidate_literal T S hd
   exact ⟨dom.2.1,fun q hq=>by have:=dom.2.2.1 q hq;omega⟩)
 have slots:=Nat.mul_le_mul_left (rule4CandidateBudget (leaves S).length+1) n
 simp only [admittedRule4Meter,admittedRule4Budget]
 omega
end Universal233.Rule5PendantLocalWork
