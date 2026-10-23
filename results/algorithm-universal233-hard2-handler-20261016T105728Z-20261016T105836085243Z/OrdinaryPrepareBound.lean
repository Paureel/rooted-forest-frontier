import OrdinaryPrepareSource
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.PaidQueries Universal233.MafScheduler

theorem properBlockMeter_bound (T S : Tree) (U : List Nat) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) (ul : U.length≤N) :
 (properBlockMeter T S U).work≤64*(N+1)^3:=by
 have t:=meterLeaves_cap T N tn;have s:=meterLeaves_cap S N sn
 have tl:=Nat.le_trans (leaves_nodes T) tn;have sl:=Nat.le_trans (leaves_nodes S) sn
 have n:=Nat.le_trans (meterNodup_bound U) (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right ul 1) 2))
 have point (x : Nat) (_ : x∈U) :
 (let t:=meterLeaves T;let s:=meterLeaves S;let a:=meterContains x t.value;let b:=meterContains x s.value
  (⟨a.value&&b.value,t.work+s.work+a.work+b.work+4⟩:Charged Bool)).work≤28*(N+1)^2:=by
  have a:=meterContains_bound x (leaves T);have b:=meterContains_bound x (leaves S)
  have lift:N+1≤(N+1)^2:=by simpa only [Nat.pow_one] using pow_mono N 1 2 (by decide)
  have pos:1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
  simp only [meterLeaves_value];omega
 have all:=cap_all _ U N 28 2 ul point
 change _≤32*(N+1)^3 at all
 dsimp only at all
 have n3:=cap_lift N 8 2 3 _ n (by decide)
 have pos:1≤(N+1)^3:=Nat.one_le_pow _ _ (by omega)
 simp only [properBlockMeter]
 omega

def ordinarySlotPolynomial (N : Nat):=401000*(N+1)^6

theorem ordinarySlotMeter_bound (T S : Tree) (U : List Nat) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) (ul : U.length≤N) :
 (ordinarySlotMeter T S U).work≤ordinarySlotPolynomial N:=by
 have pb:=cap_lift N 64 3 6 _ (properBlockMeter_bound T S U N tn sn ul) (by decide)
 have ta:=cap_lift N 16 2 6 _ (localTargetMeter_bound T U N tn (by omega)) (by decide)
 have sa:=cap_lift N 16 2 6 _ (localTargetMeter_bound S U N sn (by omega)) (by decide)
 change (meterRestrict U T).work+4≤16*(N+1)^6 at ta
 change (meterRestrict U S).work+4≤16*(N+1)^6 at sa
 have pos:1≤(N+1)^6:=Nat.one_le_pow _ _ (by omega)
 simp only [ordinarySlotMeter,ordinarySlotPolynomial,meterRestrict_value]
 split
 · dsimp only;omega
 · cases ht:restrict U T with
   | none=>cases hs:restrict U S <;> simp only [] <;> omega
   | some t=>cases hs:restrict U S with
    | none=>simp only [];omega
    | some s=>
     have ts:=Nat.le_trans (restricted_nodes U T t ht) tn
     have ss:=Nat.le_trans (restricted_nodes U S s hs) sn
     have pre:=meterPretest_bound t s N ts ss
     simp only [meterPretest_value]
     cases hpre:DepthOne.pretest01 t s with
     | refused=>simp only [];omega
     | rejected=>simp only [];omega
     | found c=>
      have cmem:=(DepthOne.found_spec t s c hpre).2.1
      have forest:=cap_lift N 128 3 6 _ (meterForest_bound s c N ss
       (fun v h=>Nat.le_trans (candidate_address s c cmem v h) ss)) (by decide)
      simp only [];omega

theorem ordinaryPrepareMeter_bound (T S : Tree) (Q : List (List Nat)) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) (blocks : ∀U,U∈Q→U.length≤N) :
 (ordinaryPrepareMeter T S Q).work≤(ordinarySlotPolynomial N+8)*Q.length+2:=by
 induction Q with
 | nil=>simp [ordinaryPrepareMeter]
 | cons U Q ih=>
  have head:=ordinarySlotMeter_bound T S U N tn sn (blocks U (by simp))
  have tail:=ih (by intro V mem;exact blocks V (by simp [mem]))
  simp only [ordinaryPrepareMeter,List.length_cons,Nat.mul_add,Nat.mul_one]
  omega
end OrdinaryDispatch.Hard2SourceWork
