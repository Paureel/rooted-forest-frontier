import GeneratorReceiptCosts
namespace GenericForest.BinaryProducer.Generator
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork

def DetachedGood (W M : Nat) (d : List Group) : Prop := ∀g∈d,BlockWidth W g.labels ∧ g.labels.length≤M

def Within (M q : Nat) (T : GTree) (d : List Group) (c : Addresses) : Prop :=
 size T+d.length+c.length+2*q≤M

def StateGood (W M q : Nat) (T : GTree) (d : List Group) (c : Addresses) : Prop :=
 Within M q T d c ∧ Wide W T ∧ DetachedGood W M d ∧ ∀v∈c,v.length≤M

theorem state_normalized (W M q T d c) (h : StateGood W M q T d c) :
 StateGood W M q (normalizeBits T).value d c := by
 have n:=normalize_size T
 have z:=h.1
 exact ⟨by unfold Within at z ⊢;omega,normalize_wide W T h.2.1,h.2.2⟩

theorem state_child (W M q T d c g U) (h : StateGood W M (q+1) T d c)
 (gmem : g∈(groupsBits T).value) (e : (eraseBits g.origin T).value=some U) :
 StateGood W M q U (g::d) (g.origin::c) := by
 have gs:=group_size T g gmem
 have ns:=erase_size g.origin T U e
 have gw:=groups_wide W T h.2.1 g gmem
 have ht : size T≤M:=by have a:=h.1;unfold Within at a;omega
 refine ⟨?_,erase_wide W g.origin T U h.2.1 e,?_,?_⟩
 · have a:=h.1;unfold Within at *;simp only [List.length_cons];omega
 · intro x hx;rcases List.mem_cons.mp hx with rfl|hx
   · exact ⟨gw,by omega⟩
   · exact h.2.2.1 x hx
 · intro v hv;rcases List.mem_cons.mp hv with rfl|hv
   · omega
   · exact h.2.2.2 v hv

theorem detachedBits_cost (d : List Group) : (detachedBits d).work=4*d.length+1 ∧ (detachedBits d).value.length=d.length := by
 induction d <;> simp_all [detachedBits,Nat.mul_add,Nat.mul_one]

theorem flattenGroups_cost (W M : Nat) (d : List Group) (h : DetachedGood W M d) :
 (flattenGroups d).work≤((4*W+5)*M+5)*(d.length+1) := by
 induction d with
 | nil=>simp [flattenGroups] <;> omega
 | cons g d ih=>
  have good:=h g (by simp)
  have r:=ih (fun x hx=>h x (by simp [hx]))
  have a:=appendLabels_work g.labels (flattenGroups d).value W good.1
  have m:=Nat.mul_le_mul_left (4*W+5) good.2
  simp only [flattenGroups,List.length_cons,Nat.mul_add,Nat.mul_one] at r ⊢;omega

def finishCost (W M : Nat) := (4*M+16)*M+((4*W+5)*M+5)*(M+1)+8*M+18

theorem finishBits_cost (W M : Nat) (T d c) (h : StateGood W M 0 T d c) :
 (finishBits T d c).work≤finishCost W M := by
 have a:=h.1;unfold Within at a
 have tn : size T≤M:=by omega
 have dn : d.length≤M:=by omega
 have g:=Nat.le_trans (groupsBits_cost M T tn) (Nat.mul_le_mul_left (4*M+16) tn)
 have good : DetachedGood W M (groupsBits T).value:=by
  intro x hx;exact ⟨groups_wide W T h.2.1 x hx,by have z:=group_size T x hx;omega⟩
 have f:=Nat.le_trans (flattenGroups_cost W M _ good)
  (Nat.mul_le_mul_left ((4*W+5)*M+5) (Nat.add_le_add_right (Nat.le_trans (groups_length T) tn) 1))
 have dcap:=detachedBits_cost d
 simp only [finishBits,appendSpine_work];unfold finishCost;omega

def attemptCost (M K : Nat) := 4*(M+1)+8*(M+1)*(M+1)+(4*M+16)*M+12*(K+1)+16

theorem attemptBits_cost (W M q K C : Nat) (f : GTree→List Group→Addresses→Charged Receipt)
 (caps : ∀t d c,CounterCap K (f t d c).value)
 (T d c g) (h : StateGood W M (q+1) T d c) (gm : g∈(groupsBits T).value)
 (hf : ∀U,(eraseBits g.origin T).value=some U→(f U (g::d) (g.origin::c)).work≤C) :
 (attemptBits f T d c g).work≤C+attemptCost M K := by
 have hn:=h.1;unfold Within at hn
 have gs:=group_size T g gm
 have rp:=meterAddressEq_bound g.origin []
 have dp:=meterVertexContains_bound g.origin c M (by omega)
 have er:=Nat.le_trans (eraseBits_cost M g.origin T (by omega)) (Nat.mul_le_mul_left (4*M+16) (by omega : size T≤M))
 have dup:=Nat.mul_le_mul_left (8*(M+1)) (show c.length+1≤M+1 by omega)
 dsimp only [attemptBits]
 split
 · dsimp only [Charged.work];unfold attemptCost;omega
 · split
   · dsimp only [Charged.work];unfold attemptCost;omega
   · cases he : (eraseBits g.origin T).value with
     | none=>simp only;unfold attemptCost;omega
     | some U=>
      have fcap:=hf U he
      have child:=childBits_cost K (f U (g::d) (g.origin::c)).value (caps _ _ _)
      simp only;unfold attemptCost;omega

def localCost (W M K : Nat) := treeUnit W M*M+chooseCost W M+finishCost W M+2*attemptCost M K+
 36*(2*(K+1)+1)+18+12*(K+3)+4+16

theorem stepBits_cost (W M q K C R : Nat) (kp : 1≤K) (rp : 1≤R)
 (f : GTree→List Group→Addresses→Charged Receipt)
 (caps : ∀t d c,CounterCap K (f t d c).value)
 (records : ∀t d c,recordCount (f t d c).value≤R)
 (work : ∀t d c,StateGood W M q t d c→(f t d c).work≤C)
 (T d c) (h : StateGood W M (q+1) T d c) :
 (stepBits f T d c).work≤2*C+localCost W M K+4*R := by
 have n:=state_normalized W M (q+1) T d c h
 have ns : size T≤M:=by have z:=h.1;unfold Within at z;omega
 have nn : size (normalizeBits T).value≤M:=Nat.le_trans (normalize_size T) ns
 have nc:=Nat.le_trans (normalizeBits_cost W M T ns h.2.1) (Nat.mul_le_mul_left (treeUnit W M) ns)
 have ch:=chooseBits_cost W M (normalizeBits T).value nn
 have finish:=finishBits_cost W M (normalizeBits T).value d c
  ⟨by have z:=n.1;unfold Within at *;omega,n.2⟩
 have chosen:=chooseBits_mem (normalizeBits T).value
 have ac (g : Group) (gm : g∈(groupsBits (normalizeBits T).value).value) :
  (attemptBits f (normalizeBits T).value d c g).work≤C+attemptCost M K := by
  apply attemptBits_cost W M q K C f caps _ _ _ _ n gm
  intro U he;exact work _ _ _ (state_child W M q _ d c g U n gm he)
 dsimp only [stepBits]
 cases he : (chooseBits (normalizeBits T).value).value with
 | finish=>simp only;unfold localCost;omega
 | refuse why=>simp only;unfold localCost;omega
 | one g=>
  have a:=ac g (chosen.1 g he)
  have ca:=attemptBits_cap K kp f caps (normalizeBits T).value d c g
  have p:=prefixBits_cost (K+1) _ ca
  simp only;unfold localCost;omega
 | two a b=>
  have members:=chosen.2 a b he
  have x:=ac a members.1;have y:=ac b members.2
  have xc:=attemptBits_cap K kp f caps (normalizeBits T).value d c a
  have yc:=attemptBits_cap K kp f caps (normalizeBits T).value d c b
  have zr:=attemptBits_records f R rp records (normalizeBits T).value d c a
  have z:=combineBits_cost (K+1) _ _ xc yc
  have p:=prefixBits_cost (K+2) _ (combineBits_cap (K+1) _ _ xc yc)
  simp only;unfold localCost;omega
end GenericForest.BinaryProducer.Generator
