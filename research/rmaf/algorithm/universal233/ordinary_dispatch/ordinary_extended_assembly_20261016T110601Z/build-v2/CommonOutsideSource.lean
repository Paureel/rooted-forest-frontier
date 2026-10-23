import CommonSetupBinding
import CommonAgreementConsumer
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph Rule5PrefixLocalWork
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence

/-- A returned pretest cut is a literal member of its finite source list. -/
theorem pretest_candidate (T S : Tree) {c : Option RMAF.Vertex}
 (h : DepthOne.pretest01 T S=.found c) : c∈DepthOne.candidates S := by
 unfold DepthOne.pretest01 at h
 split at h
 · split at h
   · contradiction
   · rename_i c' hc
     cases DepthOne.Result.found.inj h
     exact (best_spec _ _ _ _ hc).1
 · contradiction

def relabelBlockMeter (a b : Nat) : List Nat→Charged (List Nat)
 | []=>⟨[],1⟩
 | x::xs=>let r:=relabelBlockMeter a b xs;⟨swap a b x::r.value,r.work+5⟩

theorem relabel_block_value (a b : Nat) (xs : List Nat) :
 (relabelBlockMeter a b xs).value=xs.map (swap a b) := by induction xs <;> simp_all [relabelBlockMeter]

theorem relabel_block_work (a b : Nat) (xs : List Nat) :
 (relabelBlockMeter a b xs).work=5*xs.length+1 := by induction xs <;> simp_all [relabelBlockMeter] <;> omega

def relabelForestMeter (a b : Nat) : List (List Nat)→Charged (List (List Nat))
 | []=>⟨[],1⟩
 | B::F=>let x:=relabelBlockMeter a b B;let r:=relabelForestMeter a b F
           ⟨x.value::r.value,x.work+r.work+2⟩

theorem relabel_forest_value (a b : Nat) (F : List (List Nat)) :
 (relabelForestMeter a b F).value=relabelForest (swap a b) F := by
 induction F <;> simp_all [relabelForestMeter,relabel_block_value,relabelForest]

theorem relabel_forest_work (a b : Nat) (F : List (List Nat)) :
 (relabelForestMeter a b F).work=5*F.flatten.length+3*F.length+1 := by
 induction F <;> simp_all [relabelForestMeter,relabel_block_work] <;> omega

def outsideExtensionMeter (d : Setup) (FY : List (List Nat)) : Charged (List (List Nat)) :=
 let r:=relabelForestMeter d.x d.gamma ([d.x]::FY);⟨r.value,r.work+2⟩

theorem outside_extension_value (d : Setup) (FY : List (List Nat)) :
 (outsideExtensionMeter d FY).value=outsideExtension d FY := by
 simp only [outsideExtensionMeter,relabel_forest_value,outsideExtension]

theorem outside_extension_work (d : Setup) (FY : List (List Nat)) (M : Nat)
 (payload : Rule5LocalWork.cells FY≤M) : (outsideExtensionMeter d FY).work≤5*M+11 := by
 simp only [outsideExtensionMeter,relabel_forest_work,List.flatten_cons,List.length_append,List.length_cons,List.length_nil]
 unfold Rule5LocalWork.cells at payload
 omega

def outsideReplyMeter (d : Setup) (FY : List (List Nat)) : Charged (Option (List (List Nat))) :=
 let pre:=meterPretest d.myT d.myS
 match pre.value with
 | .found c=>let r:=meterForest d.myS c;⟨some r.value,pre.work+r.work+3⟩
 | .rejected=>let r:=outsideExtensionMeter d FY;⟨some r.value,pre.work+r.work+3⟩
 | .refused=>⟨none,pre.work+2⟩

theorem outside_reply_value (d : Setup) (FY : List (List Nat)) :
 (outsideReplyMeter d FY).value=outsideReply d FY := by
 simp only [outsideReplyMeter,meterPretest_value,outsideReply]
 cases h:DepthOne.pretest01 d.myT d.myS <;> simp only [meterForest_value,outside_extension_value]

def outsideBudget (N M : Nat) :=400000*(N+1)^6+128*(N+1)^3+5*M+15

theorem outside_reply_work (d : Setup) (FY : List (List Nat)) (N M : Nat)
 (tn : treeNodes d.myT≤N) (sn : treeNodes d.myS≤N) (payload : Rule5LocalWork.cells FY≤M) :
 (outsideReplyMeter d FY).work≤outsideBudget N M := by
 have pre:=meterPretest_bound d.myT d.myS N tn sn
 have ext:=outside_extension_work d FY M payload
 simp only [outsideReplyMeter]
 cases hp:(meterPretest d.myT d.myS).value with
 | refused=>unfold outsideBudget;dsimp only;omega
 | rejected=>unfold outsideBudget;dsimp only;omega
 | found c=>
  have mem:=pretest_candidate d.myT d.myS (by simpa only [meterPretest_value] using hp)
  have f:=meterForest_bound d.myS c N sn (fun v hv=>Nat.le_trans (candidate_address d.myS c mem v hv) sn)
  unfold outsideBudget
  dsimp only;omega
end Universal233.Rule5ExecutionSource
