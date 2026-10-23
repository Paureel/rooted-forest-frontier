import StoredMax
namespace OrdinaryDispatch.StoredNumeric
open RMAF Universal233.WholeSourceWork Universal233.CoreWork
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.CheckCorrespondence

def freshPair (T S : GenericForest.BinaryProvider.Tree) : Charged (Bits×Bits) :=
 let a:=leavesCopy T;let b:=leavesCopy S
 let labels:=appendLabels a.value b.value
 let maximum:=maximumBlock labels.value
 let rho:=incrementBits maximum.value
 let gamma:=incrementBits rho.value
 let rcopy:=copyBits rho.value;let gcopy:=copyBits gamma.value
 ⟨(rcopy.value,gcopy.value),a.work+b.work+labels.work+maximum.work+rho.work+gamma.work+rcopy.work+gcopy.work+12⟩

@[simp] theorem freshPair_value (T S : GenericForest.BinaryProvider.Tree) :
 decode (freshPair T S).value.1=OrdinaryCommonSplit.Source.labelMax (leaves (treeValue T)++leaves (treeValue S))+1 ∧
 decode (freshPair T S).value.2=OrdinaryCommonSplit.Source.labelMax (leaves (treeValue T)++leaves (treeValue S))+2 := by
 simp [freshPair,copyBits_value,incrementBits_value,maximumBlock_value,leavesCopy_value,appendLabels_value,blockValue_append,leaves_projection,Nat.add_assoc]

theorem freshPair_width (B : Nat) (T S : GenericForest.BinaryProvider.Tree)
 (tc : TreeWidth B T) (sc : TreeWidth B S) :
 (freshPair T S).value.1.length≤B+1 ∧ (freshPair T S).value.2.length≤B+2 := by
 have cap : BlockWidth B (leavesBits T++leavesBits S) := by
  intro x hx;rcases List.mem_append.1 hx with h|h
  · exact tc x h
  · exact sc x h
 have mx:=maximumBlock_width B _ cap
 have r:=successor_width (maximumBlock (leavesBits T++leavesBits S)).value
 have g:=successor_width (incrementBits (maximumBlock (leavesBits T++leavesBits S)).value).value
 simp only [freshPair,copyBits_value,appendLabels_value,leavesCopy_value]
 exact ⟨by omega,by omega⟩

def freshPairFee (N B : Nat) : Nat :=
 2*(GenericForest.ScalarBits.beta B*(8*(N+1)^2))+(4*B+5)*N+1+
 32*(B+1)*(2*N+1)+12*(B+1)+12*(B+2)+(4*(B+1)+1)+(4*(B+2)+1)+12

theorem freshPair_work (N B : Nat) (T S : GenericForest.BinaryProvider.Tree)
 (tn : treeNodes (treeValue T)≤N) (sn : treeNodes (treeValue S)≤N)
 (tc : TreeWidth B T) (sc : TreeWidth B S) : (freshPair T S).work≤freshPairFee N B := by
 have a:=leavesCopy_projects T B tc;have b:=leavesCopy_projects S B sc
 have ap:=Nat.mul_le_mul_left (GenericForest.ScalarBits.beta B) (meterLeaves_cap (treeValue T) N tn)
 have bp:=Nat.mul_le_mul_left (GenericForest.ScalarBits.beta B) (meterLeaves_cap (treeValue S) N sn)
 have lt : (leavesBits T).length≤N := by rw [←blockValue_length,leaves_projection];exact Nat.le_trans (leaves_nodes _) tn
 have ls : (leavesBits S).length≤N := by rw [←blockValue_length,leaves_projection];exact Nat.le_trans (leaves_nodes _) sn
 have append:=appendLabels_work (leavesBits T) (leavesBits S) B tc
 have appendcap:=Nat.mul_le_mul_left (4*B+5) lt
 have cap : BlockWidth B (leavesBits T++leavesBits S) := by
  intro x hx;rcases List.mem_append.1 hx with h|h
  · exact tc x h
  · exact sc x h
 have mx:=maximumBlock_width B _ cap
 have maximum:=maximumBlock_work B _ cap
 have scaled:=Nat.mul_le_mul_left (32*(B+1)) (show (leavesBits T++leavesBits S).length+1≤2*N+1 by simp only [List.length_append];omega)
 have rho:=successor_work (maximumBlock (leavesBits T++leavesBits S)).value
 have rwid:=successor_width (maximumBlock (leavesBits T++leavesBits S)).value
 have gamma:=successor_work (incrementBits (maximumBlock (leavesBits T++leavesBits S)).value).value
 have gwid:=successor_width (incrementBits (maximumBlock (leavesBits T++leavesBits S)).value).value
 simp only [Projects] at a b
 simp only [freshPair,freshPairFee,leavesCopy_value,appendLabels_value,copyBits_work]
 omega

/-- The exact checked source builder allocates these two fresh identifiers. -/
theorem source_build_markers (T S : RMAF.Tree) (X Y : List Nat) (p : RMAF.Vertex)
 (d : OrdinaryCommonSplit.Caller.Setup) (h : OrdinaryCommonSplit.Source.buildSetup T S X Y p=some d) :
 d.rho=OrdinaryCommonSplit.Source.labelMax (leaves T++leaves S)+1 ∧
 d.gamma=OrdinaryCommonSplit.Source.labelMax (leaves T++leaves S)+2 := by
 unfold OrdinaryCommonSplit.Source.buildSetup at h
 split at h
 · split at h
   · split at h
     · split at h
       · split at h
         · split at h
           · simp at h
           · split at h
             · split at h
               · dsimp only at h
                 split at h
                 · cases Option.some.inj h;exact ⟨rfl,rfl⟩
                 · simp at h
               · simp at h
             · simp at h
         · simp at h
     · simp at h
   · simp at h
 · simp at h

theorem freshPair_source_site (T S : GenericForest.BinaryProvider.Tree) (X Y : List Nat) (p : RMAF.Vertex)
 (d : OrdinaryCommonSplit.Caller.Setup)
 (built : OrdinaryCommonSplit.Source.buildSetup (treeValue T) (treeValue S) X Y p=some d) :
 decode (freshPair T S).value.1=d.rho ∧ decode (freshPair T S).value.2=d.gamma := by
 have source:=source_build_markers (treeValue T) (treeValue S) X Y p d built
 have value:=freshPair_value T S
 omega
end OrdinaryDispatch.StoredNumeric
