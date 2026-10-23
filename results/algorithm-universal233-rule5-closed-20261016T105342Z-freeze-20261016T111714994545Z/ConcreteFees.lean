import CommonSoundLocal
namespace Universal233.Rule5ClosedSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.FastOrdinary
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5CommonSelector Rule5SelectedLocalWork
open ClassifierCheckFee PaidLiteralDecisionWork

def source (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b q : Nat) : Charged Rule5OrdinaryDispatch.Result :=
 dispatchSource cb W checkFee (literalFee T S a b) T S a b q

theorem source_value (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b q : Nat) :
 (source cb W T S a b q).value=Rule5OrdinaryDispatch.dispatch cb T S a b q := dispatch_source_value _ _ _ _ _ _ _ _ _

def calls (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b q : Nat) :=dispatchCalls cb W checkFee (literalFee T S a b) T S a b q

theorem source_split (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b q : Nat) :
 (source cb W T S a b q).work=(source cb (fun _ _ _=>0) T S a b q).work+
 GenericForest.FrontierWork.queryWork W (calls cb W T S a b q) := dispatch_source_split _ _ _ _ _ _ _ _ _

theorem literal_domain_bound (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex)
 (sel:(finalMeter checkFee T S a b).value=some (.remaining d (.second u v)))
 (j : LiteralCall) (dom:LiteralCallDomain T S a b d u v j) :
 literalFee T S a b j≤literalBudget ((leaves T).length+(leaves S).length) := by
 have p:=final_payload checkFee T S a b sel
 exact literal_call_work T S a b d u v j dom p.2.2.2.1 p.2.2.2.2 p.1

theorem selected_concrete_local (cb : Ordinary) (sound : CallbackSound cb)
 {T S : Tree} {i : RMAF.Vertex} {a b : Nat} (ch:CherryAt T i a b) (ad:admitted T S a b=true)
 (hp:DepthOne.proper T S=true) (q L : Nat) {z : FinalSelection}
 (sel:(finalMeter checkFee T S a b).value=some z)
 (tlabs:∀x,x∈leaves T→x<2^L) (slabs:∀x,x∈leaves S→x<2^L) :
 (runSelectedSource cb (fun _ _ _=>0) checkFee (literalFee T S a b) T S a b q z).work≤
 selectedPrefixBudget T S (checkCap ((leaves T).length+(leaves S).length))
  (literalBudget ((leaves T).length+(leaves S).length)) z+
 selectedForestDebit cb checkFee (literalFee T S a b) T S a b q z := by
 cases z with
 | «prefix» s=>
  have h:=selectedArmSource_local cb checkFee T S a b q hp sel
  simp only [runSelectedSource,selectedPrefixBudget,selectedForestDebit];omega
 | remaining d z=>cases z with
  | first u v=>
   have h:=selectedArmSource_local cb checkFee T S a b q hp sel
   simp only [runSelectedSource,selectedPrefixBudget,selectedForestDebit];omega
  | third u v=>
   have h:=selectedArmSource_local cb checkFee T S a b q hp sel
   simp only [runSelectedSource,selectedPrefixBudget,selectedForestDebit];omega
  | one e=>
   have h:=common_sound_source_local cb sound checkFee ch ad sel q
   simp only [runSelectedSource,selectedPrefixBudget,selectedForestDebit];omega
  | second u v=>
   have h:=solve_selected_prefix_work cb (fun _ _ _=>0) checkFee (literalFee T S a b) T S a b q L
    (checkCap ((leaves T).length+(leaves S).length)) (literalBudget ((leaves T).length+(leaves S).length))
    tlabs slabs (check_fee_bound _ L) (literal_domain_bound T S a b)
   simp only [runSelectedSource,selectedPrefixBudget,selectedForestDebit,paidSelectedSource];omega

theorem dispatch_concrete_local (cb : Ordinary) (sound : CallbackSound cb)
 {T S : Tree} {i : RMAF.Vertex} {a b : Nat} (ch:CherryAt T i a b) (ad:admitted T S a b=true)
 (hp:DepthOne.proper T S=true) (q L : Nat) {z : FinalSelection}
 (sel:(finalMeter checkFee T S a b).value=some z)
 (tlabs:∀x,x∈leaves T→x<2^L) (slabs:∀x,x∈leaves S→x<2^L) :
 (source cb (fun _ _ _=>0) T S a b q).work≤
 finalBudget (leaves T).length (leaves S).length (checkCap ((leaves T).length+(leaves S).length))+
 selectedPrefixBudget T S (checkCap ((leaves T).length+(leaves S).length))
  (literalBudget ((leaves T).length+(leaves S).length)) z+
 selectedForestDebit cb checkFee (literalFee T S a b) T S a b q z+2 := by
 have c:=final_source_work T S a b L tlabs slabs
 have s:=selected_concrete_local cb sound ch ad hp q L sel tlabs slabs
 simp only [source,dispatchSource,sel,finalSourceMeter] at *;omega
end Universal233.Rule5ClosedSource
