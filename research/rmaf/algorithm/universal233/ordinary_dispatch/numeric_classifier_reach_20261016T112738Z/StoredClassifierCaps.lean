import StoredBadClassifier
namespace OrdinaryDispatch.StoredNumeric.ClassifierReach
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
open OrdinaryDispatch.StoredNumeric.ProducerBinding Universal233.WholeSourceWork Universal233.CoreWork

@[simp] theorem prependCherries_length (b : Bool) (cs : List CherryBits) : (prependCherries b cs).value.length=cs.length := by
 induction cs <;> simp_all [prependCherries]

theorem cherriesBits_length (T : GenericForest.BinaryProvider.Tree) : (cherriesBits T).value.length≤treeNodes (treeValue T) := by
 induction T with
 | leaf x=>simp [cherriesBits,treeValue,treeNodes]
 | node l r il ir=>cases l <;> cases r <;> simp only [cherriesBits,copyBits_value,appendSpine_value,List.length_append,prependCherries_length,List.length_singleton,treeValue,treeNodes] at * <;> omega

def cherryUnit (N B : Nat) :=8*B+64*(N+1)
theorem cherriesBits_work (N B : Nat) (T : GenericForest.BinaryProvider.Tree)
 (tc : TreeWidth B T) (tn : treeNodes (treeValue T)≤N) : (cherriesBits T).work≤cherryUnit N B*treeNodes (treeValue T) := by
 induction T with
 | leaf x=>simp only [cherriesBits,treeValue,treeNodes,Nat.mul_one,cherryUnit];omega
 | node l r il ir=>
  have ln : treeNodes (treeValue l)≤N:=by simp only [treeValue,treeNodes] at tn;omega
  have rn : treeNodes (treeValue r)≤N:=by simp only [treeValue,treeNodes] at tn;omega
  have a:=il (treeWidth_left B l r tc) ln;have b:=ir (treeWidth_right B l r tc) rn
  have al:=cherriesBits_length l;have bl:=cherriesBits_length r
  cases l with
  | leaf x=>
   cases r with
   | leaf y=>
    have xc : x.length≤B:=tc x (by simp [leavesBits])
    have yc : y.length≤B:=tc y (by simp [leavesBits])
    simp only [cherriesBits,copyBits_work,treeValue,treeNodes,cherryUnit];omega
   | node u v=>
    simp only [cherriesBits,prependCherries_work,appendSpine_work,prependCherries_length,treeValue,treeNodes,Nat.mul_add,Nat.mul_one,cherryUnit] at *;omega
  | node u v=>
   simp only [cherriesBits,prependCherries_work,appendSpine_work,prependCherries_length,treeValue,treeNodes,Nat.mul_add,Nat.mul_one,cherryUnit] at *;omega

theorem candidatesFrom_provenance (S : GenericForest.BinaryProvider.Tree) (cs : List CherryBits) (d : CandidateBits)
 (h : d∈(candidatesFrom S cs).value) :
 ∃c,c∈cs ∧ d.parent=c.parent ∧ d.a=c.a ∧ d.b=c.b ∧ d.originalCuts=(pendantBits S c.a c.b).value := by
 induction cs with
 | nil=>simp [candidatesFrom] at h
 | cons c cs ih=>
  simp only [candidatesFrom,List.mem_cons] at h
  rcases h with rfl|h
  · exact ⟨c,by simp,rfl,rfl,rfl,rfl⟩
  · obtain ⟨e,he,eq⟩:=ih h;exact ⟨e,by simp [he],eq⟩

@[simp] theorem candidatesFrom_length (S : GenericForest.BinaryProvider.Tree) (cs : List CherryBits) :
 (candidatesFrom S cs).value.length=cs.length := by induction cs <;> simp_all [candidatesFrom]

theorem findClass_mem (p : Universal233.CherryBranching.Priority) (cs : List CandidateBits) (c : CandidateBits)
 (h : (findClass p cs).value=some c) : c∈cs := by
 induction cs with
 | nil=>simp [findClass] at h
 | cons d ds ih=>
  simp only [findClass] at h
  split at h
  · cases Option.some.inj h;exact List.mem_cons_self
  · exact List.mem_cons_of_mem d (ih h)

theorem selectCandidatesBits_mem (cs : List CandidateBits) (p : Universal233.CherryBranching.Priority) (c : CandidateBits)
 (h : (selectCandidatesBits cs).value=some (p,c)) : c∈cs := by
 unfold selectCandidatesBits at h
 cases a : (findClass .common cs).value with
 | some d=>simp only [a,Option.some.injEq,Prod.mk.injEq] at h;rcases h with ⟨rfl,rfl⟩;exact findClass_mem _ _ _ a
 | none=>
  simp only [a] at h
  cases b : (findClass .one cs).value with
  | some d=>simp only [b,Option.some.injEq,Prod.mk.injEq] at h;rcases h with ⟨rfl,rfl⟩;exact findClass_mem _ _ _ b
  | none=>
   simp only [b] at h
   cases v : (findClass .high cs).value with
   | some d=>simp only [v,Option.some.injEq,Prod.mk.injEq] at h;rcases h with ⟨rfl,rfl⟩;exact findClass_mem _ _ _ v
   | none=>
    simp only [v] at h
    cases q : cs.head? with
    | none=>simp [q] at h
    | some d=>simp only [q,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h;rcases h with ⟨rfl,rfl⟩;exact List.mem_of_head? q

/-- a,b are the actual original stored leaf arrays of the selected cherry;
its parent and every pendant cut are original unary addresses. -/
theorem selectedPriority_provenance (N : Nat) (T S : GenericForest.BinaryProvider.Tree)
 (p : Universal233.CherryBranching.Priority) (c : CandidateBits)
 (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N)
 (h : (selectPriorityBits T S).value=some (p,c)) :
 c.a∈leavesBits T ∧ c.b∈leavesBits T ∧ c.parent.length≤N ∧
 c.originalCuts=(pendantBits S c.a c.b).value ∧ c.originalCuts.length≤N ∧ ∀v∈c.originalCuts,v.length≤N := by
 have mem:=selectCandidatesBits_mem (candidatesBits T S).value p c h
 obtain ⟨d,hd,hp,ha,hb,hcuts⟩:=candidatesFrom_provenance S (cherriesBits T).value c mem
 have pr:=cherriesBits_provenance T d hd
 have ps:=pendantBits_caps N S c.a c.b sn
 rw [←ha,←hb] at hcuts
 exact ⟨ha.symm▸pr.1,hb.symm▸pr.2.1,by rw [hp];omega,hcuts,by rw [hcuts];exact ps.1,by rw [hcuts];exact ps.2⟩

theorem selectedBad_caps (N B : Nat) (T S : GenericForest.BinaryProvider.Tree) (a b : Bits) (d : BadBits)
 (sc : TreeWidth B S) (sn : treeNodes (treeValue S)≤N) (h : (selectBadBits T S a b).value=some d) :
 d.c∈leavesBits S ∧ d.c.length≤B ∧ d.badArc.length≤N ∧ d.singletonArc.length≤N := by
 have pr:=selectedBad_provenance T S a b d h
 have pc:=pendantBits_caps N S a b sn
 exact ⟨pr.2.2,sc d.c pr.2.2,pc.2 d.badArc pr.1,pc.2 d.singletonArc pr.2.1⟩

/-- This closes the previous c projection/provenance premises with the actual
selected finite classifier output. The builder still performs its own guards. -/
theorem classified_payload_source_site (T S : GenericForest.BinaryProvider.Tree) (a b : Bits) (d : BadBits)
 (sel : (selectBadBits T S a b).value=some d) (setup : OrdinaryCommonSplit.Caller.Setup)
 (built : OrdinaryCommonSplit.Source.buildSetup (treeValue T) (treeValue S)
  (Universal233.HardParent.subtreeLabels (treeValue S) d.badArc)
  (Universal233.Rule5CommonSelector.outsideLabels (treeValue S) (decode a) (decode b) (badValue d)) d.badArc=some setup) :
 let out:=(commonSelectedPayload T S a b d.c d.badArc).value
 decode out.rho=setup.rho ∧ decode out.gamma=setup.gamma ∧
 [targetValue out.tx,targetValue out.sx,targetValue out.ty,targetValue out.sy,targetValue out.mxT,targetValue out.mxS,targetValue out.myT,targetValue out.myS]=
 [some setup.tx,some setup.sx,some setup.ty,some setup.sy,some setup.mxT,some setup.mxS,some setup.myT,some setup.myS] := by
 exact commonSelectedPayload_source_site T S a b d.c (badValue d) d.badArc setup rfl built

theorem classified_payload_step (T S U V : GenericForest.BinaryProvider.Tree) (a b : Bits) (d : BadBits)
 (sel : (selectBadBits T S a b).value=some d) (setup : OrdinaryCommonSplit.Caller.Setup)
 (built : OrdinaryCommonSplit.Source.buildSetup (treeValue T) (treeValue S)
  (Universal233.HardParent.subtreeLabels (treeValue S) d.badArc)
  (Universal233.Rule5CommonSelector.outsideLabels (treeValue S) (decode a) (decode b) (badValue d)) d.badArc=some setup)
 (hu : some U∈payloadTrees (commonSelectedPayload T S a b d.c d.badArc).value)
 (hv : some V∈payloadTrees (commonSelectedPayload T S a b d.c d.badArc).value) : OrientedStep T S U V :=
 commonSelectedPayload_checked_step T S U V a b d.c (badValue d) d.badArc setup rfl (selectedBad_provenance T S a b d sel).2.2 built hu hv
end OrdinaryDispatch.StoredNumeric.ClassifierReach
