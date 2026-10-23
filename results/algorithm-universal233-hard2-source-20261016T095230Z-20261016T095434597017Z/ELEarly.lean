import ELRule4Raw
namespace OrdinaryDispatch.EarlyLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence

theorem multiply_powers (k C N p r : Nat) :
 k*(N+1)^p*(C*(N+1)^r)=(k*C)*(N+1)^(p+r) := by
 rw [Nat.pow_add]
 ac_rfl

structure ChoiceMeasured (T S : Tree) where
 value : Option (Rule4.Choice T S)
 work : Nat
 checks : List (Rule4.RawChoice×Bool)

def meterFirstChoice (T S : Tree) (hp : Rule4.Priority T S) : List Rule4.RawChoice→ChoiceMeasured T S
 | []=>⟨none,1,[]⟩
 | x::xs=>let g:=meterLocalGuard T S x
   if h:g.value=true then
    let proof : Rule4.LocalGuard T S x:=of_decide_eq_true ((meterLocalGuard_value T S x).symm.trans h)
    ⟨some ⟨x,hp,proof⟩,g.work+4,[(x,true)]⟩
   else let r:=meterFirstChoice T S hp xs
        ⟨r.value,g.work+r.work+4,(x,false)::r.checks⟩
@[simp] theorem meterFirstChoice_value (T S : Tree) (hp : Rule4.Priority T S) (xs : List Rule4.RawChoice) :
 (meterFirstChoice T S hp xs).value=Rule4.firstChoice T S hp xs := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>by_cases h:Rule4.LocalGuard T S x <;>
   simp [meterFirstChoice,Rule4.firstChoice,meterLocalGuard_value,h,ih]

theorem meterFirstChoice_bound (T S : Tree) (hp : Rule4.Priority T S) (xs : List Rule4.RawChoice) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) (heads : ∀x∈xs,x.cHead.length≤N) :
 (meterFirstChoice T S hp xs).work≤(2048*(N+1)^4+4)*(xs.length+1) := by
 induction xs with
 | nil=>simp [meterFirstChoice]
 | cons x xs ih=>
  have a:=meterLocalGuard_bound T S x N tn sn (heads x (by simp))
  have b:=ih (fun y hy=>heads y (by simp [hy]))
  simp only [Nat.mul_add,Nat.mul_one] at b
  simp only [meterFirstChoice,List.length_cons,Nat.mul_add,Nat.mul_one]
  split <;> simp only [ChoiceMeasured.work] <;> omega

def meterRule4Select (T S : Tree) : Charged (Option (Rule4.Choice T S)) :=
 let p:=meterRule4Priority T S
 if h:p.value=true then
  let hp : Rule4.Priority T S:=of_decide_eq_true ((meterRule4Priority_value T S).symm.trans h)
  let raw:=meterRawChoices T S;let first:=meterFirstChoice T S hp raw.value
  ⟨first.value,p.work+raw.work+first.work+4⟩
 else ⟨none,p.work+2⟩
@[simp] theorem meterRule4Select_value (T S) : (meterRule4Select T S).value=Rule4.select T S := by
 by_cases h:Rule4.Priority T S <;>
  simp [meterRule4Select,Rule4.select,meterRule4Priority_value,h]

theorem meterRule4Select_bound (T S : Tree) (N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterRule4Select T S).work≤262144*(N+1)^6 := by
 have p:=cap_lift N 16384 5 6 _ (meterRule4Priority_bound T S N tn sn) (by decide)
 have raw:=meterRawChoices_bound T S N tn sn
 have rl:=rawChoices_length T S N tn sn
 have pos4 : 1≤(N+1)^4:=Nat.one_le_pow _ _ (by omega)
 have pos2 : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
 have pos6 : 1≤(N+1)^6:=Nat.one_le_pow _ _ (by omega)
 simp only [meterRule4Select,meterRawChoices_value]
 split
 · rename_i h
   let hp : Rule4.Priority T S:=of_decide_eq_true ((meterRule4Priority_value T S).symm.trans h)
   have f:=meterFirstChoice_bound T S hp (Rule4.rawChoices T S) N tn sn
    (fun x hx=>Nat.le_trans (rawChoice_head T S x hx) sn)
   have coeff : 2048*(N+1)^4+4≤2052*(N+1)^4:=by omega
   have len : (Rule4.rawChoices T S).length+1≤17*(N+1)^2:=by omega
   have scale:=Nat.mul_le_mul coeff len
   have ff : (meterFirstChoice T S hp (Rule4.rawChoices T S)).work≤34884*(N+1)^6:=
    Nat.le_trans f (by simpa only [multiply_powers] using scale)
   change (meterRule4Priority T S).work+(meterRawChoices T S).work+
    (meterFirstChoice T S hp (Rule4.rawChoices T S)).work+4≤_
   omega
 · simp only [Charged.work];omega

/-- Both orientation calls are retained. Rule4 suffixes may be charged even
when an earlier source priority succeeds; this is an explicit upper evaluator. -/
def meterEarly (T S : Tree) : Charged (FastOrdinary.Early T S) :=
 let f:=meterSelect T S;let r:=meterSelect S T
 let a:=meterRule4Select T S;let b:=meterRule4Select S T
 ⟨match f.value,r.value with
  | some (.common,c),_=>.common false c
  | _,some (.common,d)=>.common true d
  | some (.one,c),_=>.one false c
  | _,some (.one,d)=>.one true d
  | some (.high,c),_=>.high false c
  | _,some (.high,d)=>.high true d
  | some (.hard2,c),some (.hard2,d)=>match a.value with
    | some s=>.rule4Forward s
    | none=>match b.value with | some s=>.rule4Reverse s | none=>.hard2 c d
  | _,_=>.refused,
  f.work+r.work+a.work+b.work+8⟩
@[simp] theorem meterEarly_value (T S) : (meterEarly T S).value=FastOrdinary.early T S := by
 simp only [meterEarly,meterSelect_value,meterRule4Select_value,FastOrdinary.early]
 repeat first | rfl | split

theorem meterEarly_bound (T S : Tree) (N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterEarly T S).work≤1048576*(N+1)^6 := by
 have f:=cap_lift N 2048 5 6 _ (meterSelect_bound T S N tn sn) (by decide)
 have r:=cap_lift N 2048 5 6 _ (meterSelect_bound S T N sn tn) (by decide)
 have a:=meterRule4Select_bound T S N tn sn;have b:=meterRule4Select_bound S T N sn tn
 have pos : 1≤(N+1)^6:=Nat.one_le_pow _ _ (by omega)
 simp only [meterEarly];omega

end OrdinaryDispatch.EarlyLocalWork
