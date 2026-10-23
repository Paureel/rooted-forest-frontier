import BitPartition
set_option maxRecDepth 2000
namespace GenericForest.ScalarBits
open RMAF Universal233 Universal233.WholeSourceWork GenericForest.CheckCorrespondence

def TreeCap (W : Nat) (T : Tree) := LabelCap W (leaves T)
theorem treeCap_left (W : Nat) (l r : Tree) (h : TreeCap W (.node l r)) : TreeCap W l :=
 fun x hx=>h x (by simp [leaves,hx])
theorem treeCap_right (W : Nat) (l r : Tree) (h : TreeCap W (.node l r)) : TreeCap W r :=
 fun x hx=>h x (by simp [leaves,hx])
theorem restricted_cap (W : Nat) (B : List Nat) (T U : Tree) (cap : TreeCap W T)
 (h : restrict B T=some U) : TreeCap W U := by
 intro x hx
 rw [RestrictionBridge.restrict_labels T U B h] at hx
 exact cap x (List.mem_filter.mp hx).1

def bitSameShape (W : Nat) : Tree→Tree→Charged Bool
 | .leaf a,.leaf b=>let e:=referenceEq W a b;⟨e.value,e.work⟩
 | .node a b,.node c d=>
  let ac:=bitSameShape W a c;let bd:=bitSameShape W b d;let ad:=bitSameShape W a d;let bc:=bitSameShape W b c
  ⟨(ac.value&&bd.value)||(ad.value&&bc.value),ac.work+bd.work+ad.work+bc.work+4*beta W⟩
 | _,_=>⟨false,4*beta W⟩

theorem bitSameShape_refines (W : Nat) (T S : Tree) (tc : TreeCap W T) (sc : TreeCap W S) :
 Refines W (bitSameShape W T S) (meterSameShape T S) := by
 induction T generalizing S with
 | leaf a=>
  cases S with
  | leaf b=>exact referenceEq_refines W a b (tc a (by simp [leaves])) (sc b (by simp [leaves]))
  | node l r=>simp [Refines,bitSameShape,meterSameShape,Nat.mul_comm]
 | node a b iha ihb=>
  cases S with
  | leaf c=>simp [Refines,bitSameShape,meterSameShape,Nat.mul_comm]
  | node c d=>
   have ac:=iha c (treeCap_left W a b tc) (treeCap_left W c d sc)
   have ad:=iha d (treeCap_left W a b tc) (treeCap_right W c d sc)
   have bc:=ihb c (treeCap_right W a b tc) (treeCap_left W c d sc)
   have bd:=ihb d (treeCap_right W a b tc) (treeCap_right W c d sc)
   simp only [Refines] at ac ad bc bd ⊢
   simp only [bitSameShape,meterSameShape]
   constructor
   · simp only [ac.1,ad.1,bc.1,bd.1]
   · simp only [Nat.mul_add,Nat.mul_comm (beta W) 4];omega

def bitRestrict (W : Nat) (B : List Nat) : Tree→Charged (Option Tree)
 | .leaf x=>let m:=bitContains W x B;⟨if m.value then some (.leaf x) else none,m.work+4*beta W⟩
 | .node l r=>let a:=bitRestrict W B l;let b:=bitRestrict W B r
               ⟨match a.value,b.value with
                | none,none=>none | some x,none=>some x | none,some y=>some y | some x,some y=>some (.node x y),
                a.work+b.work+4*beta W⟩

theorem bitRestrict_refines (W : Nat) (B : List Nat) (T : Tree) (bc : LabelCap W B) (tc : TreeCap W T) :
 Refines W (bitRestrict W B T) (meterRestrict B T) := by
 induction T with
 | leaf x=>
  have m:=bitContains_refines W x B (tc x (by simp [leaves])) bc
  simp only [Refines] at m ⊢
  simp only [bitRestrict,meterRestrict,m.1]
  constructor
  · trivial
  · simp only [Nat.mul_add,Nat.mul_comm (beta W) 4];omega
 | node l r ihl ihr=>
  have a:=ihl (treeCap_left W l r tc)
  have b:=ihr (treeCap_right W l r tc)
  simp only [Refines] at a b ⊢
  simp only [bitRestrict,meterRestrict,a.1,b.1]
  constructor
  · trivial
  · simp only [Nat.mul_add,Nat.mul_comm (beta W) 4];omega

def bitRestrictionAgrees (W : Nat) (T S : Tree) (B : List Nat) : Charged Bool :=
 let a:=bitRestrict W B T;let b:=bitRestrict W B S
 match a.value,b.value with
 | some u,some v=>let c:=bitSameShape W u v;⟨c.value,a.work+b.work+c.work+4*beta W⟩
 | _,_=>⟨false,a.work+b.work+4*beta W⟩

theorem bitRestrictionAgrees_refines (W : Nat) (T S : Tree) (B : List Nat)
 (tc : TreeCap W T) (sc : TreeCap W S) (bc : LabelCap W B) :
 Refines W (bitRestrictionAgrees W T S B) (meterRestrictionAgrees T S B) := by
 have a:=bitRestrict_refines W B T bc tc
 have b:=bitRestrict_refines W B S bc sc
 simp only [Refines] at a b ⊢
 simp only [bitRestrictionAgrees,meterRestrictionAgrees,a.1,b.1]
 cases ht : (meterRestrict B T).value with
 | none=>
  cases hs : (meterRestrict B S).value <;> simp only [ht,hs]
  all_goals refine ⟨by trivial,?_⟩
  all_goals simp only [Nat.mul_add,Nat.mul_comm (beta W) 4];omega
 | some u=>
  cases hs : (meterRestrict B S).value with
  | none=>
   simp only [ht,hs]
   constructor
   · trivial
   · simp only [Nat.mul_add,Nat.mul_comm (beta W) 4];omega
  | some v=>
   have uc:=restricted_cap W B T u tc (by simpa only [meterRestrict_value] using ht)
   have vc:=restricted_cap W B S v sc (by simpa only [meterRestrict_value] using hs)
   have c:=bitSameShape_refines W u v uc vc
   simp only [ht,hs]
   constructor
   · exact c.1
   · have h:=c.2;simp only [Nat.mul_add,Nat.mul_comm (beta W) 4];omega
end GenericForest.ScalarBits
