import Hard2OutputGenerationSource
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork CoreProgram VertexGeometry
open GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.Hard2PaidLocal Universal233.Hard2Overlap Universal233.PaidAssembly

def localAddressCap (T : Tree) (N : Nat) :=2*(16*(treeNodes T+3)*treeNodes T+4*(N+1)+3)+3

theorem localCap_address (T : Tree) (N : Nat) (l : Local)
 (address : match l with | .keep=>True | .single v=>v.length≤N | .joint v w=>v.length≤N ∧ w.length≤N) :
 WholeSourceWork.localCap T l≤localAddressCap T N := by
 cases l <;> simp_all [WholeSourceWork.localCap,colorCap,localAddressCap] <;> omega

def uniformTaggedCap (T : Tree) (N : Nat) :=8*(N+1)+3*localAddressCap T N+8

theorem taggedCap_address (T : Tree) (A B : List Nat) (c : Colors) (N : Nat)
 (al : A.length≤N) (bl : B.length≤N)
 (address : ∀l,l∈[c.a,c.b,c.c]→match l with | .keep=>True | .single v=>v.length≤N | .joint v w=>v.length≤N ∧ w.length≤N) :
 taggedCap T A B c≤uniformTaggedCap T N := by
 have a:=localCap_address T N c.a (address c.a (by simp))
 have b:=localCap_address T N c.b (address c.b (by simp))
 have d:=localCap_address T N c.c (address c.c (by simp))
 unfold taggedCap uniformTaggedCap
 omega

theorem sideTaggedMeter_bound (A B D : List Nat) (x N : Nat)
 (al : A.length≤N) (bl : B.length≤N) (dl : D.length≤N) :
 (sideTaggedMeter A B D x).work≤12*(N+1)+8 := by
 have a:=meterContains_bound x A;have b:=meterContains_bound x B;have d:=meterContains_bound x D
 simp only [sideTaggedMeter]
 split
 · simp only [Charged.work];omega
 · split <;> simp only [Charged.work] <;> omega

def outputCountCap (S : Tree) (q : Nat) :=3*2^(min q ((leaves S).length-1)+1)
def outputCallCap (S T : Tree) (N q : Nat) :=generationEnvelope S q+(leaves S).length*uniformTaggedCap T N

theorem wholeOutputs_uniform (S T : Tree) (A B : List Nat) (c : Colors) (N q : Nat)
 (al : A.length≤N) (bl : B.length≤N)
 (address : ∀l,l∈[c.a,c.b,c.c]→match l with | .keep=>True | .single v=>v.length≤N | .joint v w=>v.length≤N ∧ w.length≤N) :
 (wholeOutputsMeter S T A B c q).work≤outputCallCap S T N q ∧
 (wholeOutputsMeter S T A B c q).value.length≤outputCountCap S q := by
 constructor
 · exact Nat.le_trans (wholeOutputsMeter_bound S T A B c q)
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (taggedCap_address T A B c N al bl address)) _)
 · simp only [wholeOutputsMeter,generatedOutputsMeter_value,outputCountCap]
   exact generate_output_count S _ q

def KindSize (N : Nat) : Kind→Prop
 | .clique v=>v.length≤N
 | .four v w=>v.length≤N ∧ w.length≤N
 | .diagonal v w=>v.length≤N ∧ w.length≤N
 | .vertex v=>v.length≤N
 | .side D=>D.length≤N

def outputKindCap (S T : Tree) (N q : Nat) :=4*outputCallCap S T N q+12*outputCountCap S q+16

theorem kindOutputsMeter_bound (kind : Kind) (S T : Tree) (A B : List Nat) (N q : Nat)
 (al : A.length≤N) (bl : B.length≤N) (ks : KindSize N kind) :
 (kindOutputsMeter kind S T A B q).work≤outputKindCap S T N q ∧
 (kindOutputsMeter kind S T A B q).value.length≤4*outputCountCap S q := by
 have point (c : Colors)
  (addr : ∀l,l∈[c.a,c.b,c.c]→match l with | .keep=>True | .single v=>v.length≤N | .joint v w=>v.length≤N ∧ w.length≤N) :=
  wholeOutputs_uniform S T A B c N q al bl addr
 cases kind with
 | clique v=>
  have a:=point ⟨.keep,.single v,.single v⟩ (by intro l h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> simp_all [KindSize])
  have b:=point ⟨.single v,.keep,.single v⟩ (by intro l h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> simp_all [KindSize])
  have c:=point ⟨.single v,.single v,.keep⟩ (by intro l h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> simp_all [KindSize])
  simp only [kindOutputsMeter,appendOutputsMeter,List.length_append,outputKindCap]
  constructor <;> omega
 | four v w=>
  have a:=point ⟨.keep,.single v,.single w⟩ (by intro l h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> simp_all [KindSize])
  have b:=point ⟨.keep,.joint v w,.keep⟩ (by intro l h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> simp_all [KindSize])
  have c:=point ⟨.single v,.keep,.single w⟩ (by intro l h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> simp_all [KindSize])
  have d:=point ⟨.single v,.single w,.keep⟩ (by intro l h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> simp_all [KindSize])
  simp only [kindOutputsMeter,appendOutputsMeter,List.length_append,outputKindCap]
  constructor <;> omega
 | diagonal v w=>
  have a:=point ⟨.keep,.joint v w,.keep⟩ (by intro l h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> simp_all [KindSize])
  have b:=point ⟨.single v,.keep,.single w⟩ (by intro l h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> simp_all [KindSize])
  simp only [kindOutputsMeter,appendOutputsMeter,List.length_append,outputKindCap]
  constructor <;> omega
 | vertex v=>
  have a:=point ⟨.single v,.keep,.keep⟩ (by intro l h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> simp_all [KindSize])
  have b:=point ⟨.keep,.single v,.keep⟩ (by intro l h;simp only [List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> simp_all [KindSize])
  simp only [kindOutputsMeter,appendOutputsMeter,List.length_append,outputKindCap]
  constructor <;> omega
 | side D=>
  have h:=generatedOutputsMeter_bound S (sideTaggedMeter A B D) q
  have c:=charged_color_sum (leaves S) (sideTaggedMeter A B D) (12*(N+1)+8)
   (by intro x _;exact sideTaggedMeter_bound A B D x N al bl ks)
  have k:12*(N+1)+8≤uniformTaggedCap T N:=by unfold uniformTaggedCap localAddressCap;omega
  have mul:=Nat.mul_le_mul_left (leaves S).length k
  have count:=generate_output_count S (fun x=>(sideTaggedMeter A B D x).value) q
  simp only [kindOutputsMeter,generatedOutputsMeter_value,outputKindCap,outputCallCap,outputCountCap]
  constructor <;> omega
end OrdinaryDispatch.Hard2SourceWork
