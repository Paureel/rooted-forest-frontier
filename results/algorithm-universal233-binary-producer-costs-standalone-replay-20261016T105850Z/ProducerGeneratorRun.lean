import ProducerGeneratorStep
namespace GenericForest.BinaryProducer.Generator
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork

def fuelBits {A : Type} (q : Bits) : List A→Charged Capacity
 | []=>⟨[],1⟩
 | _::xs=>let e:=leBits [true] q
           if e.value then let d:=subtractBits q [true];let r:=fuelBits d.value xs
                           ⟨()::r.value,e.work+d.work+r.work+8⟩
           else ⟨[],e.work+4⟩
@[simp] theorem fuelBits_length {A : Type} (q : Bits) (xs : List A) :
 (fuelBits q xs).value.length=min (decode q) xs.length := by
 induction xs generalizing q with
 | nil=>simp [fuelBits]
 | cons x xs ih=>
  dsimp only [fuelBits]
  simp only [leBits_value,decode,bit,ite_true,Nat.mul_zero,Nat.add_zero]
  split
  · rename_i h
    simp only [decide_eq_true_eq] at h
    simp only [List.length_cons,ih,subtractBits_value,decode,bit,ite_true,Nat.mul_zero,Nat.add_zero]
    omega
  · rename_i h
    simp only [decide_eq_true_eq] at h
    simp only [List.length_nil,List.length_cons]
    omega

theorem fuelBits_cost {A : Type} (B : Nat) (q : Bits) (xs : List A) (bp : 1≤B) (qw : q.length≤B) :
 (fuelBits q xs).work≤(34*(B+2)+8)*(xs.length+1) := by
 induction xs generalizing q with
 | nil=>simp [fuelBits] <;> omega
 | cons x xs ih=>
  have e:=(compare_family_work [true] q).2.1
  have d:=subtractBits_work q [true]
  have dl:=subtractBits_length q [true]
  have dw : (subtractBits q [true]).value.length≤B:=by simp only [List.length_cons,List.length_nil] at dl;omega
  have r:=ih (subtractBits q [true]).value dw
  dsimp only [fuelBits]
  split <;> dsimp only [Charged.work]
  all_goals simp only [List.length_cons,List.length_nil,Nat.mul_add,Nat.mul_one] at *;omega

def runBits : Capacity→GTree→List Group→Addresses→Charged Receipt
 | [],t,d,c=>let r:=stepBits (fun _ _ _=>⟨⟨[],[],[],[],[true]⟩,8⟩) t d c;⟨r.value,r.work+4⟩
 | _::fuel,t,d,c=>let r:=stepBits (runBits fuel) t d c;⟨r.value,r.work+4⟩
theorem runBits_value (fuel : Capacity) (T : GTree) (d : List Group) (c : Addresses) :
 receiptValue (runBits fuel T d c).value=Universal233.CoreProgram.run fuel.length (gtreeValue T) (groupsValue d) c := by
 induction fuel generalizing T d c with
 | nil=>
  exact stepBits_value _ _ (by intros;rfl) T d c
 | cons u fuel ih=>
  exact stepBits_value _ _ ih T d c

theorem nodupLabels_value (B : Block) : (nodupLabels B).value=decide ((blockValue B).Nodup) := by
 let C:=(prepareCapacity B []).value
 have cap:=prepareCapacity_spec B []
 exact (nodupLabels_projects C.length B cap.1).1.trans (GenericForest.CheckCorrespondence.meterNodup_value _)

/-- Source budget is converted by traversing the actual remaining leaf spine.
No decoded mathematical Nat controls executable recursion. -/
def generateBits (S : BinaryProvider.Tree) (color : Bits→Charged Color) (q : Bits) : Charged Receipt:=
 let a:=leavesCopy S;let nd:=nodupLabels a.value
 if nd.value then
  let fuel:=fuelBits q a.value.tail;let t:=fromTreeBits color [] S;let r:=runBits fuel.value t.value [] []
  ⟨r.value,a.work+nd.work+fuel.work+t.work+r.work+16⟩
 else ⟨⟨[],["duplicate original label"],[],[],[]⟩,a.work+nd.work+8⟩

theorem generateBits_value (S : BinaryProvider.Tree) (color : Bits→Charged Color) (native : Nat→Nat)
 (ih : ∀x,colorValue (color x).value=native (decode x)) (q : Bits) :
 receiptValue (generateBits S color q).value=Universal233.CoreProgram.generate (treeValue S) native (decode q) := by
 dsimp only [generateBits]
 simp only [leavesCopy_value,nodupLabels_value,leaves_projection]
 unfold Universal233.CoreProgram.generate
 split
 · rename_i proper
   simp only [decide_eq_true_eq] at proper
   simp only [proper,decide_true,ite_true]
   simp only [runBits_value,fromTreeBits_value color native ih,groupsValue,List.map_nil,fuelBits_length,List.length_tail]
   have e:=congrArg List.length (leaves_projection S)
   simp only [blockValue_length] at e
   rw [e]
 · rename_i bad
   simp only [decide_eq_true_eq] at bad
   simp [bad,receiptValue,decode]
end GenericForest.BinaryProducer.Generator
