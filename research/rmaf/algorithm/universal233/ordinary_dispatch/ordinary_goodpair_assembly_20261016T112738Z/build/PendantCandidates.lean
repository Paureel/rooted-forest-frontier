import PendantPartitionWork
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching

def candidateRowsMeter (S : Tree) : List CherryRow→Measured (List Candidate)
 | []=>⟨[],1⟩
 | (p,a,b)::cs=>let e:=cutsMeter S a b;let r:=candidateRowsMeter S cs
                ⟨⟨p,a,b,e.value⟩::r.value,e.work+r.work+6⟩

theorem candidate_rows_value (S : Tree) (cs : List CherryRow) :
 (candidateRowsMeter S cs).value=cs.map fun (p,a,b)=>⟨p,a,b,cuts S a b⟩ := by
 induction cs with
 | nil=>rfl
 | cons c cs ih=>rcases c with ⟨p,a,b⟩;simp only [candidateRowsMeter,List.map_cons,cuts_value,ih]

theorem candidate_rows_work (S : Tree) (cs : List CherryRow) :
 (candidateRowsMeter S cs).work≤(cutsBudget (leaves S).length+6)*cs.length+1 := by
 induction cs with
 | nil=>simp [candidateRowsMeter]
 | cons c cs ih=>
   rcases c with ⟨p,a,b⟩
   have e:=cuts_work S a b
   simp only [candidateRowsMeter,List.length_cons,Nat.mul_succ]
   omega

def candidatesMeter (T S : Tree) : Measured (List Candidate) :=
 let c:=cherriesMeter T;let r:=candidateRowsMeter S c.value
 ⟨r.value,c.work+r.work+1⟩

theorem candidates_value (T S : Tree) : (candidatesMeter T S).value=candidates T S := by
 simp only [candidatesMeter,candidate_rows_value,cherries_value,candidates]

def candidatesBudget (nt ns : Nat) :=16*nt*nt+(cutsBudget ns+6)*nt+2

theorem candidates_work (T S : Tree) :
 (candidatesMeter T S).work≤candidatesBudget (leaves T).length (leaves S).length := by
 have c:=cherries_work T
 have r:=candidate_rows_work S (cherries T)
 have n:=cherries_count T
 have m:=Nat.mul_le_mul_left (cutsBudget (leaves S).length+6) n
 simp only [candidatesMeter,cherries_value,candidatesBudget]
 omega

theorem candidates_count (T S : Tree) : (candidatesMeter T S).value.length≤(leaves T).length := by
 rw [candidates_value]
 simpa only [candidates,List.length_map] using cherries_count T

theorem candidate_literal (T S : Tree) {c : Candidate} (mem : c∈(candidatesMeter T S).value) :
 c.originalCuts=(cutsMeter S c.a c.b).value ∧
 c.originalCuts.length≤2*(leaves S).length ∧
 (∀p,p∈c.originalCuts →p.length+1≤(leaves S).length) ∧
 c.parent.length+1≤(leaves T).length ∧ c.a∈leaves T ∧ c.b∈leaves T := by
 rw [candidates_value] at mem
 obtain ⟨⟨p,a,b⟩,row,eq⟩:=List.mem_map.1 mem
 cases eq
 have cap:=cherry_row_payload T p a b (by rw [cherries_value];exact row)
 exact ⟨(cuts_value S a b).symm,by simpa only [cuts_value] using cuts_count S a b,
   fun q hq=>cuts_address S a b (by rw [cuts_value];exact hq),cap⟩

def earlierAllMeter : List Candidate→Measured Bool
 | []=>⟨true,1⟩
 | c::cs=>if c.originalCuts.length==2 then
             let r:=earlierAllMeter cs;⟨r.value,c.originalCuts.length+r.work+2⟩
           else ⟨false,c.originalCuts.length+2⟩

theorem earlier_all_value (cs : List Candidate) :
 (earlierAllMeter cs).value=cs.all (fun c=>c.originalCuts.length==2) := by
 induction cs with
 | nil=>rfl
 | cons c cs ih=>simp only [earlierAllMeter,List.all_cons];split <;> simp_all

theorem earlier_all_work (cs : List Candidate) (N : Nat)
 (cap : ∀c,c∈cs →c.originalCuts.length≤N) :
 (earlierAllMeter cs).work≤(N+2)*cs.length+1 := by
 induction cs with
 | nil=>simp [earlierAllMeter]
 | cons c cs ih=>
   have h:=cap c (by simp)
   have tail:=ih (fun d hd=>cap d (by simp [hd]))
   simp only [earlierAllMeter]
   split <;> (try dsimp only) <;> simp only [List.length_cons,Nat.mul_succ] <;> omega

def earlierMeter (T S : Tree) : Measured Bool :=
 let c:=candidatesMeter T S;let a:=earlierAllMeter c.value
 ⟨a.value,c.work+a.work+1⟩

theorem earlier_value (T S : Tree) : (earlierMeter T S).value=Rule5Local.earlierClear T S := by
 simp only [earlierMeter,earlier_all_value,candidates_value,Rule5Local.earlierClear]

def earlierBudget (nt ns : Nat) :=candidatesBudget nt ns+(2*ns+2)*nt+2

theorem earlier_work (T S : Tree) :
 (earlierMeter T S).work≤earlierBudget (leaves T).length (leaves S).length := by
 have c:=candidates_work T S
 have n:=candidates_count T S
 have a:=earlier_all_work (candidatesMeter T S).value (2*(leaves S).length)
   (fun d hd=>(candidate_literal T S hd).2.1)
 have slots:=Nat.mul_le_mul_left (2*(leaves S).length+2) n
 simp only [earlierMeter,earlierBudget]
 omega
end Universal233.Rule5PendantLocalWork
