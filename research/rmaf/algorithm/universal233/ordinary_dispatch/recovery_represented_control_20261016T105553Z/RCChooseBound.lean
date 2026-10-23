import RCChoose
set_option maxRecDepth 4000
namespace OrdinaryDispatch.RecoveryControlBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits

theorem chooseCore_work (W N : Nat) (gs : List BitGroup) (t : BitTree)
 (positive : 1≤W) (caps : GroupCaps W N gs) (size : gs.length≤N)
 (words : TreeWords W t) (shape : footprint (viewTree t)≤N) :
 (chooseCore W gs t).work≤48*groupFee W N*(N+1)^2 := by
 let G:=groupFee W N;let K:=G*(N+1)^2
 have sq:N+1≤(N+1)^2:=by rw [Nat.pow_two];simpa only [Nat.one_mul] using Nat.mul_le_mul_right (N+1) (show 1≤N+1 by omega)
 have gk:G≤K:=by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left G (Nat.one_le_pow 2 (N+1) (by omega))
 have pos:64≤K:=Nat.le_trans (groupFee_positive W N) gk
 have linear:G*(N+1)≤K:=Nat.mul_le_mul_left G sq
 have find: (findUnique W gs gs).work≤20*K:=by
  have a:=findUnique_work W N gs gs positive caps caps size
  have b:=Nat.mul_le_mul_left (20*G*(N+1)) (Nat.add_le_add_right size 1)
  have eq:20*G*(N+1)*(N+1)=20*K:=by simp only [K,Nat.pow_two,Nat.mul_assoc]
  rw [eq] at b
  exact Nat.le_trans a b
 have mixed:(mixedBits t).work≤8*K:=by
  have a:=mixedBits_work W N t words shape
  have b:=Nat.mul_le_mul_left (8*G) (Nat.le_succ N)
  have c:=Nat.mul_le_mul_left 8 linear
  exact Nat.le_trans a (Nat.le_trans b (by simpa only [Nat.mul_assoc] using c))
 cases gs with
 | nil=>simp only [chooseCore];calc _≤48*K:=by omega
                                 _=48*groupFee W N*(N+1)^2:=by simp only [K,G,Nat.mul_assoc]
 | cons first rest=>
  have uniform:(allColor first.color (first::rest)).work≤3*K:=by
   have a:=allColor_work W N first.color (first::rest) (caps first (by simp)).2.1 caps
   have b:=Nat.mul_le_mul_left (3*G) (Nat.add_le_add_right size 1)
   have c:=Nat.mul_le_mul_left 3 linear
   exact Nat.le_trans a (Nat.le_trans b (by simpa only [Nat.mul_assoc] using c))
  simp only [chooseCore]
  split
  · simp only [Charged.work]
    calc _≤48*K:=by omega
         _=48*groupFee W N*(N+1)^2:=by simp only [K,G,Nat.mul_assoc]
  · cases hf:(findUnique W (first::rest) (first::rest)).value with
    | some g=>simp only [hf];calc _≤48*K:=by omega
                                _=48*groupFee W N*(N+1)^2:=by simp only [K,G,Nat.mul_assoc]
    | none=>
     simp only [hf]
     cases hc:(mixedBits t).value with
     | none=>simp only [hc];calc _≤48*K:=by omega
                                _=48*groupFee W N*(N+1)^2:=by simp only [K,G,Nat.mul_assoc]
     | some p=>
      rcases p with ⟨a,b⟩
      have cp:=mixedBits_caps W N t words shape a b hc
      have eq: (ownedEqual a.color b.color).work+8≤2*G:=word_test_fee W N a.color b.color cp.1.2.1 cp.2.2.1
      have ca:=closed_group_fee W N a cp.1;have cb:=closed_group_fee W N b cp.2
      have close:(closePair (a,b)).work≤2*G:=by simp only [closePair];omega
      simp only [hc]
      split <;> simp only [Charged.work] <;>
       (calc _≤48*K:=by omega
             _=48*groupFee W N*(N+1)^2:=by simp only [K,G,Nat.mul_assoc])

theorem chooseBits_work (W N : Nat) (t : BitTree) (positive : 1≤W)
 (words : TreeWords W t) (shape : footprint (viewTree t)≤N) :
 (chooseBits W t).work≤4096*(W+4)*(N+1)^3 := by
 let G:=groupFee W N;let K:=G*(N+1)^2
 have len:=Nat.le_trans (rawGroups_length t) shape
 have caps:=rawGroups_caps W N t words shape
 have core:=chooseCore_work W N (rawGroups t) t positive caps len words shape
 have groups:=groupsBits_work W N t words shape
 have close:=closeGroups_work W N (rawGroups t) caps
 have sq:N+1≤(N+1)^2:=by rw [Nat.pow_two];simpa only [Nat.one_mul] using Nat.mul_le_mul_right (N+1) (show 1≤N+1 by omega)
 have linear:G*(N+1)≤K:=Nat.mul_le_mul_left G sq
 have gk:G≤K:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left G (Nat.one_le_pow 2 (N+1) (by omega))
 have pos:64≤K:=Nat.le_trans (groupFee_positive W N) gk
 have groupsK:(groupsBits t).work≤K:=by
  have a:=Nat.mul_le_mul_left G (Nat.le_succ N)
  exact Nat.le_trans groups (Nat.le_trans a linear)
 have closeK:(closeGroups (rawGroups t)).work≤K:=Nat.le_trans close (Nat.le_trans (Nat.mul_le_mul_left G (Nat.add_le_add_right len 1)) linear)
 have coreK:(chooseCore W (rawGroups t) t).work≤48*K:=by simpa only [K,G,Nat.mul_assoc] using core
 simp only [chooseBits,groupsBits_value]
 calc _≤64*K:=by omega
      _=4096*(W+4)*(N+1)^3:=by
       rw [show 4096=64*64 from rfl]
       simp only [K,G,groupFee,Nat.pow_succ,Nat.pow_zero,Nat.mul_one]
       ac_rfl

/-- Exact source priority/refusals, concrete polynomial work and copied retained
choice. Count width remains explicit until supplied by the actual caller. -/
theorem represented_choose (W N : Nat) (t : BitTree) (positive : 1≤W)
 (words : TreeWords W t) (shape : footprint (viewTree t)≤N) (countFit : N<2^W) :
 viewChoice (chooseBits W t).value=CoreProgram.choose (viewTree t) ∧
 (chooseBits W t).work≤4096*(W+4)*(N+1)^3 ∧
 choiceCells (chooseBits W t).value≤2*((W+4)*N)+1 := by
 have fits:=Nat.lt_of_le_of_lt (Nat.le_trans (rawGroups_length t) shape) countFit
 exact ⟨chooseBits_value W t fits,chooseBits_work W N t positive words shape,
  choiceCells_cap W N _ (chooseBits_caps W N t words shape)⟩
end OrdinaryDispatch.RecoveryControlBits
