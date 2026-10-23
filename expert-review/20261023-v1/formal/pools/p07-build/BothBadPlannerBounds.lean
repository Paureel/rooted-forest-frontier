import BothBadPlanSource
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.BothBad Universal233.PaidQueries Universal233.BinaryCheap

theorem entriesMeter_bound (q Q : Nat) (mode : Mode) (os : List CoreProgram.Output)
 (cuts:∀o,o∈os→o.sourceCuts.length≤Q) :
 (entriesMeter q mode os).work≤(2*Q+20)*os.length+2:=by
 induction os with
 | nil=>simp [entriesMeter]
 | cons o os ih=>
   have h:=cuts o (by simp)
   have t:=ih (by intro p hm;exact cuts p (by simp [hm]))
   simp only [entriesMeter,List.length_cons,Nat.mul_add,Nat.mul_one]
   omega

theorem yesSideMeter_bound (A D : List Nat) (N : Nat) (al:A.length≤N) (dl:D.length≤N) :
 (yesSideMeter A D).work≤8*(N+1)^2:=by
 apply hard2_cap_filter _ A N 4 1 al
 intro x _
 have h:=meterContains_bound x D
 simp only [Nat.pow_one];omega

theorem noSideMeter_bound (A D : List Nat) (N : Nat) (al:A.length≤N) (dl:D.length≤N) :
 (noSideMeter A D).work≤10*(N+1)^2:=by
 apply hard2_cap_filter _ A N 6 1 al
 intro x _
 have h:=meterContains_bound x D
 simp only [Nat.pow_one];omega

theorem knownOneMeter_bound (T S : Tree) (A : List Nat) (N : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (al:A.length≤N) :
 (knownOneMeter T S A).work≤401000*(N+1)^6:=by
 have ta:=cap_lift N 16 2 6 _ (localTargetMeter_bound T A N tn (by omega)) (by decide)
 have sa:=cap_lift N 16 2 6 _ (localTargetMeter_bound S A N sn (by omega)) (by decide)
 change (meterRestrict A T).work+4≤16*(N+1)^6 at ta
 change (meterRestrict A S).work+4≤16*(N+1)^6 at sa
 have pos:1≤(N+1)^6:=Nat.one_le_pow _ _ (by omega)
 simp only [knownOneMeter,meterRestrict_value]
 cases ht:restrict A T with
 | none=>cases hs:restrict A S <;> simp only [] <;> omega
 | some t=>cases hs:restrict A S with
   | none=>simp only [];omega
   | some s=>
     have ts:=Nat.le_trans (restricted_nodes A T t ht) tn
     have ss:=Nat.le_trans (restricted_nodes A S s hs) sn
     have pre:=meterPretest_bound t s N ts ss
     simp only [meterPretest_value]
     cases hp:DepthOne.pretest01 t s with
     | refused=>simp only [];omega
     | rejected=>simp only [];omega
     | found c=>cases c with
       | none=>simp only [];omega
       | some v=>
         have cmem:=(DepthOne.found_spec t s (some v) hp).2.1
         have f:=cap_lift N 128 3 6 _ (meterForest_bound s (some v) N ss
          (fun w hw=>Nat.le_trans (candidate_address s (some v) cmem w hw) ss)) (by decide)
         simp only [];omega

def cheapPlanFixedPolynomial (N : Nat):=402000*(N+1)^6

theorem cheapPlanMeter_bound (S T : Tree) (A B C D : List Nat) (q N Q : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (al:A.length≤N) (dl:D.length≤N)
 (cheap opposite : List CoreProgram.Output)
 (cc:∀o,o∈cheap→o.sourceCuts.length≤Q) (oc:∀o,o∈opposite→o.sourceCuts.length≤Q) :
 (cheapPlanMeter S T A B C D q cheap opposite).work≤
 cheapPlanFixedPolynomial N+(2*Q+24)*(cheap.length+opposite.length)+64:=by
 have y:=cap_lift N 8 2 6 _ (yesSideMeter_bound A D N al dl) (by decide)
 have n:=cap_lift N 10 2 6 _ (noSideMeter_bound A D N al dl) (by decide)
 have yl:(yesSideMeter A D).value.length≤N:=by
  rw [yesSideMeter_value];exact Nat.le_trans (List.length_filter_le _ _) al
 have nl:(noSideMeter A D).value.length≤N:=by
  rw [noSideMeter_value];exact Nat.le_trans (List.length_filter_le _ _) al
 have gy:=cap_lift N 128 2 6 _ (meterRestrictionAgrees_bound S T _ N (by omega) (by omega) yl) (by decide)
 have gn:=cap_lift N 128 2 6 _ (meterRestrictionAgrees_bound S T _ N (by omega) (by omega) nl) (by decide)
 have known:=knownOneMeter_bound T S A N tn sn al
 have ca:=entriesMeter_bound q Q .ordinary cheap cc
 have cp:(entriesMeter q .ordinary cheap).value.length≤cheap.length:=by rw [entriesMeter_value];exact entries_length q .ordinary cheap
 have op (mode : Mode):=(entriesMeter_bound q Q mode opposite oc)
 have pos:1≤(N+1)^6:=Nat.one_le_pow _ _ (by omega)
 simp only [cheapPlanMeter,cheapPlanFixedPolynomial]
 split
 · cases hk:(knownOneMeter T S A).value with
   | none=>simp only [];omega
   | some F=>
     have cb:=op (.retained A B C F)
     simp only [appendEntriesMeter]
     simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at ca cb ⊢
     omega
 · have cb:=op .full
   simp only [appendEntriesMeter]
   simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at ca cb ⊢
   omega
end OrdinaryDispatch.Hard2SourceWork
