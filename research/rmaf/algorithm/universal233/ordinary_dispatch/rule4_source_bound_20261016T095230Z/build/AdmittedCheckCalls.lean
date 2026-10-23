import AdmittedRule4Guard
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching

/-- Exact named primitive bodies owned by the checker correspondence. No
selector, geometry builder or whole local caller is hidden in this interface. -/
inductive CheckRequest where
 | embedding (T : Tree) (P : List (List Nat))
 | restriction (T S : Tree) (B : List Nat)
 deriving Repr,DecidableEq

def checkValue : CheckRequest→Bool
 | .embedding T P=>pairwiseEmbeddings T P
 | .restriction T S B=>restrictionAgrees T S B

structure CheckReceipt (α : Type) where
 value : α
 work : Nat
 calls : List CheckRequest
 deriving Repr

def liftMeter {α : Type} (m : Measured α) : CheckReceipt α := ⟨m.value,m.work,[]⟩
def checkMeter (fee : CheckRequest→Nat) (r : CheckRequest) : CheckReceipt Bool := ⟨checkValue r,fee r,[r]⟩

def andSequence : List (Unit→CheckReceipt Bool)→CheckReceipt Bool
 | []=>⟨true,1,[]⟩
 | f::fs=>let a:=f ()
           if a.value then let b:=andSequence fs
            ⟨b.value,a.work+b.work+a.calls.length+1,a.calls++b.calls⟩
           else ⟨false,a.work+1,a.calls⟩

theorem and_sequence_value (fs : List (Unit→CheckReceipt Bool)) :
 (andSequence fs).value=fs.all (fun f=>(f ()).value) := by
 induction fs with
 | nil=>rfl
 | cons f fs ih=>simp only [andSequence,List.all_cons];split <;> simp_all

theorem and_sequence_work (fs : List (Unit→CheckReceipt Bool)) (B C : Nat)
 (bounds : ∀f,f∈fs →(f ()).work≤B ∧ (f ()).calls.length≤C) :
 (andSequence fs).work≤(B+C+1)*fs.length+1 := by
 induction fs with
 | nil=>simp [andSequence]
 | cons f fs ih=>
   have a:=bounds f (by simp)
   have tail:=ih (fun g hg=>bounds g (by simp [hg]))
   simp only [andSequence]
   split <;> (try dsimp only) <;> simp only [List.length_cons,Nat.mul_succ] <;> omega

theorem and_sequence_call (fs : List (Unit→CheckReceipt Bool)) {r : CheckRequest}
 (mem : r∈(andSequence fs).calls) : ∃f,f∈fs ∧ r∈(f ()).calls := by
 induction fs with
 | nil=>simp [andSequence] at mem
 | cons f fs ih=>
   simp only [andSequence] at mem
   split at mem
   · rcases List.mem_append.1 mem with h|h
     · exact ⟨f,by simp,h⟩
     · obtain ⟨g,hg,hr⟩:=ih h;exact ⟨g,by simp [hg],hr⟩
   · exact ⟨f,by simp,mem⟩

def restrictionFilterMeter (fee : CheckRequest→Nat) (T S : Tree) : List (List Nat)→CheckReceipt (List (List Nat))
 | []=>⟨[],1,[]⟩
 | B::P=>let c:=checkMeter fee (.restriction T S B);let r:=restrictionFilterMeter fee T S P
           ⟨if c.value then B::r.value else r.value,c.work+r.work+3,.restriction T S B::r.calls⟩

theorem restriction_filter_value (fee : CheckRequest→Nat) (T S : Tree) (P : List (List Nat)) :
 (restrictionFilterMeter fee T S P).value=P.filter (restrictionAgrees T S) := by
 induction P with
 | nil=>rfl
 | cons B P ih=>simp only [restrictionFilterMeter,checkMeter,checkValue,List.filter_cons,ih]

theorem restriction_filter_calls (fee : CheckRequest→Nat) (T S : Tree) (P : List (List Nat)) :
 (restrictionFilterMeter fee T S P).calls=P.map (CheckRequest.restriction T S) := by
 induction P with
 | nil=>rfl
 | cons B P ih=>simp only [restrictionFilterMeter,List.map_cons,ih]

theorem restriction_filter_work (fee : CheckRequest→Nat) (T S : Tree) (P : List (List Nat)) (K : Nat)
 (primitive : ∀B,B∈P →fee (.restriction T S B)≤K) :
 (restrictionFilterMeter fee T S P).work≤(K+3)*P.length+1 := by
 induction P with
 | nil=>simp [restrictionFilterMeter]
 | cons B P ih=>
   have a:=primitive B (by simp)
   have tail:=ih (fun C hC=>primitive C (by simp [hC]))
   simp only [restrictionFilterMeter,checkMeter,List.length_cons,Nat.mul_succ]
   omega

def CheckDomain (N L : Nat) : CheckRequest→Prop
 | .embedding T P=> (leaves T).length≤N ∧ P.length≤2*N+1 ∧ P.flatten.length≤payloadCap N+N ∧
    (∀x,x∈leaves T →x<2^L) ∧ (∀x,x∈P.flatten →x<2^L)
 | .restriction T S B=> (leaves T).length≤N ∧ (leaves S).length≤N ∧ B.length≤N ∧
    (∀x,x∈leaves T →x<2^L) ∧ (∀x,x∈leaves S →x<2^L) ∧ (∀x,x∈B →x<2^L)

theorem partition_block_domain (S : Tree) (a b : Nat) {B : List Nat}
 (mem : B∈(partitionMeter S a b).value) : B.length≤(leaves S).length ∧ B⊆leaves S := by
 simp only [partitionMeter,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at mem
 rcases mem with mem|rfl
 · rw [blocks_value] at mem
   obtain ⟨p,hp,eq⟩:=List.mem_map.1 mem
   rw [←eq,←subtree_labels_value]
   exact subtree_labels_payload S p
 · exact core_domain S a b

theorem partition_embedding_domain (T S : Tree) (a b N L : Nat)
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L) :
 CheckDomain N L (.embedding T (partitionMeter S a b).value) := by
 have p:=partition_domain S a b
 have poly:=Nat.mul_le_mul scap (Nat.mul_le_mul_left 2 scap)
 unfold CheckDomain payloadCap at *
 exact ⟨tcap,by omega,by omega,tlabs,fun x hx=>slabs x (p.2.2 hx)⟩

theorem partition_restriction_domain (T S : Tree) (a b N L : Nat) {B : List Nat}
 (tcap : (leaves T).length≤N) (scap : (leaves S).length≤N)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (mem : B∈(partitionMeter S a b).value) : CheckDomain N L (.restriction T S B) := by
 have block:=partition_block_domain S a b mem
 exact ⟨tcap,scap,by omega,tlabs,slabs,fun x hx=>slabs x (block.2 hx)⟩
end Universal233.Rule5PendantLocalWork
