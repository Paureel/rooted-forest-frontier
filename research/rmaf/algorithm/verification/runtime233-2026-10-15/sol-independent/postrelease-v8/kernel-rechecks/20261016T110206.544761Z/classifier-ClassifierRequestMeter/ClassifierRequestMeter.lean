import LiteralInterface
import HullCheckMeters
namespace Universal233.ClassifierCheckFee
open RMAF CoreWork Rule5PrefixLocalWork Rule5PendantLocalWork
open GenericForest.CheckCorrespondence

/-- Exact frozen request bodies, reusing the existing structural checker meters.
Two explicit inspections pay request dispatch and primitive invocation. -/
def requestMeter : CheckRequest→CheckReceipt Bool
 | r@(.embedding T P)=>let m:=meterPairwise T P;⟨m.value,m.work+2,[r]⟩
 | r@(.restriction T S B)=>let m:=meterRestrictionAgrees T S B;⟨m.value,m.work+2,[r]⟩

theorem request_value (r : CheckRequest) : (requestMeter r).value=checkValue r := by
 cases r <;> simp [requestMeter,checkValue]

theorem request_calls (r : CheckRequest) : (requestMeter r).calls=[r] := by
 cases r <;> rfl

/-- The formerly arbitrary fee is the implemented request's inspection bill. -/
def checkFee (r : CheckRequest) : Nat := (requestMeter r).work

theorem check_receipt_eq (r : CheckRequest) : checkMeter checkFee r=requestMeter r := by
 cases r <;> simp [checkMeter,checkFee,requestMeter,checkValue]

def requestSize (N : Nat) :=payloadCap N+2*N+1

def checkCap (N : Nat) :=120*(requestSize N+1)^5+128*(N+1)^2+2

theorem block_length_le_flatten {P : List (List Nat)} {B : List Nat} (h : B∈P) :
 B.length≤P.flatten.length := by
 induction P with
 | nil=>simp at h
 | cons C P ih=>
  rcases List.mem_cons.1 h with rfl|h
  · simp only [List.flatten_cons,List.length_append];omega
  · have tail:=ih h;simp only [List.flatten_cons,List.length_append];omega

/-- Every bounded embedding request, including invalid overlapping forests. -/
theorem embedding_work (T : Tree) (P : List (List Nat)) (N L : Nat)
 (dom : CheckDomain N L (.embedding T P)) :
 checkFee (.embedding T P)≤120*(requestSize N+1)^5+2 := by
 rcases dom with ⟨ht,hp,hflat,_,_⟩
 have nodes:=treeNodes_le_twice_leaves T
 have budget:=meterPairwise_polynomial T P (requestSize N)
  (by unfold requestSize;omega) (by unfold requestSize;omega)
  (by unfold requestSize;omega)
  (by intro B hb;have bl:=block_length_le_flatten hb;unfold requestSize;omega)
 change (meterPairwise T P).work+2≤_
 omega

/-- Both restrictions and the full unordered sameShape decision are included. -/
theorem restriction_work (T S : Tree) (B : List Nat) (N L : Nat)
 (dom : CheckDomain N L (.restriction T S B)) :
 checkFee (.restriction T S B)≤128*(N+1)^2+2 := by
 rcases dom with ⟨ht,hs,hb,_,_,_⟩
 have tn:=treeNodes_le_twice_leaves T
 have sn:=treeNodes_le_twice_leaves S
 have bill:=meterRestrictionAgrees_bound T S B N (by omega) (by omega) hb
 change (meterRestrictionAgrees T S B).work+2≤_
 omega

/-- Uniform Kc on the exact frozen CheckDomain; no truth premise is used. -/
theorem check_fee_bound (N L : Nat) (r : CheckRequest) (dom : CheckDomain N L r) :
 checkFee r≤checkCap N := by
 cases r with
 | embedding T P=>have h:=embedding_work T P N L dom;unfold checkCap;omega
 | restriction T S B=>have h:=restriction_work T S B N L dom;unfold checkCap;omega

end Universal233.ClassifierCheckFee
