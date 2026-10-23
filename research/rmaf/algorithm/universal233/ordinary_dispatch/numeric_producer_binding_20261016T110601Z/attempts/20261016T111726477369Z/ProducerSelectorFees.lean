import ProducerCommonBinding
namespace OrdinaryDispatch.StoredNumeric.ProducerBinding
open RMAF GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
open Universal233.WholeSourceWork Universal233.CoreWork GenericForest.CheckCorrespondence

def pendantFilterUnit (N H : Nat) := 4*(N+1)+16*(N+1)*(H+1)+12

theorem pendantFilter_work (N : Nat) (H V : Addresses) (paths : ∀p∈V,p.length≤N) :
 (pendantFilter H V).work≤pendantFilterUnit N H.length*(V.length+1) := by
 induction V with
 | nil=>simp [pendantFilter,pendantFilterUnit];omega
 | cons p ps ih=>
  have pc:=paths p (by simp)
  have dc:=parentCopy_work p
  have dl : (parentCopy p).value.length≤N:=by rw [parentCopy_value,List.length_dropLast];omega
  have a:=meterVertexContains_bound (parentCopy p).value H N dl
  have b:=meterVertexContains_bound p H N pc
  have r:=ih (fun v hv=>paths v (by simp [hv]))
  simp only [pendantFilter,pendantFilterUnit,List.length_cons,Nat.mul_add,Nat.mul_one] at *
  omega

def pendantSelectorFee (N B : Nat) :=
 32*(N+1)*N+beta B*((16*(N+4)+16)*(N+1)*N)+pendantFilterUnit N N*(N+1)+12

theorem pendantBits_caps (N : Nat) (S : GenericForest.BinaryProvider.Tree) (a b : Bits) (sn : treeNodes (treeValue S)≤N) :
 (pendantBits S a b).value.length≤N ∧ ∀p∈(pendantBits S a b).value,p.length≤N := by
 have sub:=pendantFilter_sublist (minimalLabels [a,b] S).value (verticesBits S).value
 have n:=verticesBits_count S
 have ps:=verticesBits_paths S
 exact ⟨Nat.le_trans sub.length_le (by omega),fun p hp=>Nat.le_trans (ps p (sub.subset hp)) sn⟩

theorem pendantBits_work (N B : Nat) (S : GenericForest.BinaryProvider.Tree) (a b : Bits)
 (sc : TreeWidth B S) (sn : treeNodes (treeValue S)≤N) (ac : a.length≤B) (bc : b.length≤B) :
 (pendantBits S a b).work≤pendantSelectorFee N B := by
 have vc:=verticesBits_cost N S sn
 have vn:=verticesBits_count S
 have vp:=verticesBits_paths S
 have mc:=(minimalLabels_projects B [a,b] S (by intro x hx;simp only [List.mem_cons,List.not_mem_nil,or_false] at hx;rcases hx with rfl|rfl <;> assumption) sc).2
 have mm:=meterMinimal_bound (blockValue [a,b]) (treeValue S) N sn
 have mn:=minimal_length (blockValue [a,b]) (treeValue S)
 have mv:=minimalLabels_value [a,b] S
 have ml : (minimalLabels [a,b] S).value.length≤N:=by rw [mv];omega
 have mf : (minimalLabels [a,b] S).work≤beta B*((16*(N+4)+16)*(N+1)*N):=by
  have p:=Nat.mul_le_mul_left (beta B) (Nat.le_trans mm (Nat.mul_le_mul_left (spanCap (blockValue [a,b]) N) sn))
  simp only [spanCap,blockValue_length,List.length_cons,List.length_nil] at p
  omega
 have fc:=pendantFilter_work N (minimalLabels [a,b] S).value (verticesBits S).value (fun p hp=>Nat.le_trans (vp p hp) sn)
 have u : pendantFilterUnit N (minimalLabels [a,b] S).value.length≤pendantFilterUnit N N:=by
  unfold pendantFilterUnit;have p:=Nat.mul_le_mul_left (16*(N+1)) (Nat.add_le_add_right ml 1);omega
 have f:=Nat.le_trans fc (Nat.mul_le_mul u (by omega : (verticesBits S).value.length+1≤N+1))
 dsimp only [pendantBits,pendantSelectorFee];omega

def subtreeSelectorFee (N B : Nat) :=4*(N+1)+leafCost N B+4

theorem subtreeLeavesBits_work (N B : Nat) (S : GenericForest.BinaryProvider.Tree) (p : RMAF.Vertex)
 (sc : TreeWidth B S) (sn : treeNodes (treeValue S)≤N) (pc : p.length≤N) :
 (subtreeLeavesBits S p).work≤subtreeSelectorFee N B := by
 have sw:=subtreeBits_work S p
 cases h : (subtreeBits S p).value with
 | none=>simp only [subtreeLeavesBits,h,subtreeSelectorFee];omega
 | some U=>
  have uw:=subtreeBits_width B S U p sc h
  have un:=Nat.le_trans (subtreeBits_nodes S U p h) sn
  have lc:=leavesCopy_cost N B U uw un
  simp only [subtreeLeavesBits,h,subtreeSelectorFee];omega

theorem subtreeUnion_caps (N B : Nat) (S : GenericForest.BinaryProvider.Tree) (ps : Addresses)
 (sc : TreeWidth B S) (sn : treeNodes (treeValue S)≤N) :
 BlockWidth B (subtreeUnion S ps).value ∧ (subtreeUnion S ps).value.length≤N*ps.length := by
 induction ps with
 | nil=>constructor;exact fun x hx=>by simp [subtreeUnion] at hx;simp [subtreeUnion]
 | cons p ps ih=>
  have cap:=subtreeLeavesBits_caps B S p sc
  have lc:=Nat.le_trans (bitsLeaves_count S) sn
  constructor
  · intro x hx;simp only [subtreeUnion,appendLabels_value,List.mem_append] at hx
    rcases hx with hx|hx
    · exact cap.1 x hx
    · exact ih.1 x hx
  · simp only [subtreeUnion,appendLabels_value,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one];omega

def subtreeUnionUnit (N B : Nat) := subtreeSelectorFee N B+(4*B+5)*N+9

theorem subtreeUnion_work (N B : Nat) (S : GenericForest.BinaryProvider.Tree) (ps : Addresses)
 (sc : TreeWidth B S) (sn : treeNodes (treeValue S)≤N) (paths : ∀p∈ps,p.length≤N) :
 (subtreeUnion S ps).work≤subtreeUnionUnit N B*(ps.length+1) := by
 induction ps with
 | nil=>simp [subtreeUnion,subtreeUnionUnit];omega
 | cons p ps ih=>
  have l:=subtreeLeavesBits_work N B S p sc sn (paths p (by simp))
  have cap:=subtreeLeavesBits_caps B S p sc
  have lc:=Nat.le_trans cap.2 (Nat.le_trans (bitsLeaves_count S) sn)
  have a:=appendLabels_work (subtreeLeavesBits S p).value (subtreeUnion S ps).value B cap.1
  have ap:=Nat.mul_le_mul_left (4*B+5) lc
  have r:=ih (fun v hv=>paths v (by simp [hv]))
  simp only [subtreeUnion,subtreeUnionUnit,List.length_cons,Nat.mul_add,Nat.mul_one] at *;omega

def coreSelectorFee (N B : Nat) := pendantSelectorFee N B+subtreeUnionUnit N B*(N+1)+leafCost N B+
 (beta B*(4*(N*N+1))+6)*(N+1)+16

theorem coreSelectorBits_work (N B : Nat) (S : GenericForest.BinaryProvider.Tree) (a b : Bits)
 (sc : TreeWidth B S) (sn : treeNodes (treeValue S)≤N) (ac : a.length≤B) (bc : b.length≤B) :
 (coreSelectorBits S a b).work≤coreSelectorFee N B := by
 have p:=pendantBits_work N B S a b sc sn ac bc
 have pc:=pendantBits_caps N S a b sn
 have u:=subtreeUnion_work N B S (pendantBits S a b).value sc sn pc.2
 have uc:=subtreeUnion_caps N B S (pendantBits S a b).value sc sn
 have up:=Nat.mul_le_mul_left (subtreeUnionUnit N B) (Nat.add_le_add_right pc.1 1)
 have ul : (subtreeUnion S (pendantBits S a b).value).value.length≤N*N:=Nat.le_trans uc.2 (Nat.mul_le_mul_left N pc.1)
 have l:=leavesCopy_cost N B S sc sn
 have ln:=Nat.le_trans (bitsLeaves_count S) sn
 have e:=excludeLabels_cost B (subtreeUnion S (pendantBits S a b).value).value (leavesBits S) uc.1 sc
 have ep:=Nat.mul_le_mul (show beta B*(4*((subtreeUnion S (pendantBits S a b).value).value.length+1))+6≤beta B*(4*(N*N+1))+6 by
  have t:=Nat.mul_le_mul_left (beta B) (Nat.mul_le_mul_left 4 (Nat.add_le_add_right ul 1));omega) (Nat.add_le_add_right ln 1)
 simp only [coreSelectorBits,leavesCopy_value,coreSelectorFee];omega

def outsideSelectorFee (N B : Nat) :=coreSelectorFee N B+4*B+1+(4*B+5)*N+1+8

theorem outsideSelectorBits_work (N B : Nat) (S : GenericForest.BinaryProvider.Tree) (a b c : Bits)
 (sc : TreeWidth B S) (sn : treeNodes (treeValue S)≤N) (ac : a.length≤B) (bc : b.length≤B) (cc : c.length≤B) :
 (outsideSelectorBits S a b c).work≤outsideSelectorFee N B := by
 have k:=coreSelectorBits_work N B S a b sc sn ac bc
 have kc:=coreSelectorBits_width B S a b sc
 have kn:=Nat.le_trans (coreSelectorBits_length S a b) (Nat.le_trans (bitsLeaves_count S) sn)
 have a:=appendLabels_work (coreSelectorBits S a b).value [(copyBits c).value] B kc
 have ap:=Nat.mul_le_mul_left (4*B+5) kn
 simp only [outsideSelectorBits,copyBits_work,outsideSelectorFee];omega

def commonSelectorsFee (N B : Nat) :=subtreeSelectorFee N B+outsideSelectorFee N B+2*(4*B+5)+16

theorem commonSelectorsBits_work (N B : Nat) (S : GenericForest.BinaryProvider.Tree) (a b c : Bits) (p : RMAF.Vertex)
 (sc : TreeWidth B S) (sn : treeNodes (treeValue S)≤N) (ac : a.length≤B) (bc : b.length≤B) (cc : c.length≤B) (pc : p.length≤N) :
 (commonSelectorsBits S a b c p).work≤commonSelectorsFee N B := by
 have X:=subtreeLeavesBits_work N B S p sc sn pc
 have Y:=outsideSelectorBits_work N B S a b c sc sn ac bc cc
 have x:=headRepresentative_work B _ (subtreeLeavesBits_caps B S p sc).1
 have y:=headRepresentative_work B _ (outsideSelectorBits_width B S a b c sc cc)
 simp only [commonSelectorsBits,commonSelectorsFee];omega
end OrdinaryDispatch.StoredNumeric.ProducerBinding
