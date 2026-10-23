import ELEarly
namespace OrdinaryDispatch.EarlyLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence

inductive Front (T S : Tree) where
 | stop (answer : Option CommonForest)
 | selected (early : FastOrdinary.Early T S)

/-- The literal nonrecursive prefix of FastOrdinary.solve, ending immediately
before recursive branch construction. It includes the repeated pretest proper. -/
def front (q : Nat) (T S : Tree) : Front T S :=
 if DepthOne.proper T S then
  match DepthOne.pretest01 T S with
  | .refused=>.stop none
  | .found c=>.stop (if DepthOne.cutCost c≤q then some (DepthOne.forest S c) else none)
  | .rejected=>.selected (FastOrdinary.early T S)
 else .stop none

def meterFront (q : Nat) (T S : Tree) : Charged (Front T S) :=
 let p:=meterOrdinaryProper T S
 if p.value then
  let d:=meterPretest T S
  match d.value with
  | .refused=>⟨.stop none,p.work+d.work+4⟩
  | .found c=>
    let f:=meterForest S c
    ⟨.stop (if DepthOne.cutCost c≤q then some f.value else none),p.work+d.work+f.work+8⟩
  | .rejected=>let e:=meterEarly T S;⟨.selected e.value,p.work+d.work+e.work+4⟩
 else ⟨.stop none,p.work+2⟩
@[simp] theorem meterFront_value (q T S) : (meterFront q T S).value=front q T S := by
 simp only [meterFront,front,meterOrdinaryProper_value,meterPretest_value,meterForest_value,meterEarly_value]
 repeat first | rfl | split

/-- Binds the found prefix to the unchanged frozen solve at every budget,
including budgets larger than the current reduced leaf count. -/
theorem front_found_solve (T S : Tree) (q : Nat) (c : Option RMAF.Vertex)
 (hp : DepthOne.proper T S=true) (found : DepthOne.pretest01 T S=.found c) :
 FastOrdinary.solve q T S=(if DepthOne.cutCost c≤q then some (DepthOne.forest S c) else none) ∧
 front q T S=.stop (FastOrdinary.solve q T S) := by
 have actual : FastOrdinary.solve q T S=(if DepthOne.cutCost c≤q then some (DepthOne.forest S c) else none) := by
  rw [FastOrdinary.solve.eq_def]
  simp only [hp,ite_true,found]
 exact ⟨actual,by simp only [front,hp,ite_true,found,actual]⟩

theorem front_rejected_binding (T S : Tree) (q : Nat)
 (hp : DepthOne.proper T S=true) (rejected : DepthOne.pretest01 T S=.rejected) :
 front q T S=.selected (FastOrdinary.early T S) := by simp [front,hp,rejected]

theorem meterFront_bound (T S : Tree) (q N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterFront q T S).work≤2097152*(N+1)^6 := by
 have p:=cap_lift N 128 2 6 _ (meterOrdinaryProper_bound T S N tn sn) (by decide)
 have d:=meterPretest_bound T S N tn sn
 have e:=meterEarly_bound T S N tn sn
 have pos : 1≤(N+1)^6:=Nat.one_le_pow _ _ (by omega)
 simp only [meterFront,meterOrdinaryProper_value,meterPretest_value]
 split
 · cases result:DepthOne.pretest01 T S with
   | refused=>simp only [result];omega
   | rejected=>simp only [result];omega
   | found c=>
    have mem:=(DepthOne.found_spec T S c result).2.1
    have f:=cap_lift N 128 3 6 _ (meterForest_bound S c N sn
      (fun v hv=>Nat.le_trans (candidate_address S c mem v hv) sn)) (by decide)
    simp only [result];omega
 · simp only [Charged.work];omega

/-- Explicit resources for a reduced current state. NT,NS may be original
sizes; Q bounds current q separately. There is no hypothesis q<=current n. -/
def ScalarDomain (T S : Tree) (q L Q : Nat) : Prop :=
 (∀x∈leaves T,x<2^L) ∧ (∀x∈leaves S,x<2^L) ∧ q≤Q

def structuralEnvelope (NT NS L Q : Nat) : Nat :=
 2097152*(NT+NS+L+Q+1)^6

theorem meterFront_resources (T S : Tree) (q NT NS L Q : Nat)
 (tn : treeNodes T≤NT) (sn : treeNodes S≤NS) (domain : ScalarDomain T S q L Q) :
 (meterFront q T S).work≤structuralEnvelope NT NS L Q := by
 exact meterFront_bound T S q (NT+NS+L+Q) (by omega) (by omega)

/-- A weighted structural model only. A binary provider must separately prove
that fee covers every unit scalar equality/inequality/increment, label copy,
comparison with q, and administrative address/counter slot in this source sheet.
It is not an assumption that the whole selector already has a cost bound. -/
def weightedFront (fee q : Nat) (T S : Tree) : Nat := fee*(meterFront q T S).work

theorem weightedFront_bound (fee q : Nat) (T S : Tree) (NT NS L Q : Nat)
 (tn : treeNodes T≤NT) (sn : treeNodes S≤NS) (domain : ScalarDomain T S q L Q) :
 weightedFront fee q T S≤fee*structuralEnvelope NT NS L Q :=
 Nat.mul_le_mul_left fee (meterFront_resources T S q NT NS L Q tn sn domain)

end OrdinaryDispatch.EarlyLocalWork
