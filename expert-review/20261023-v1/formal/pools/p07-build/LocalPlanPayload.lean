import BothBadLocalExecutionSource
import OrdinarySchedulerPayload
import Hard2FullOutputBound
import BothBadPlannerWeighted

namespace OrdinaryDispatch.Hard2SourceWork.LocalDispatchEnvelope
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence Universal233.BothBad Universal233.BinaryCheap Universal233.RankConsumer OrdinaryDispatch.EarlyLocalWork

def OutputCap (N : Nat) (o : CoreProgram.Output) : Prop :=
 o.partition.length≤N ∧ ∀U,U∈o.partition→U.length≤N

def ModeCap (N : Nat) : Mode→Prop
 | .ordinary | .full => True
 | .retained _ residual completed known =>
   residual.length≤N ∧ completed.length≤N ∧ known.length≤2 ∧ known.flatten.length≤2*N

def EntryCap (N : Nat) (e : Entry) : Prop := OutputCap N e.output ∧ ModeCap N e.mode

theorem block_le_flatten (P : List (List Nat)) (U : List Nat) (mem:U∈P) :
 U.length≤P.flatten.length := by
 induction P with
 | nil=>simp at mem
 | cons V P ih=>
   rcases List.mem_cons.1 mem with h|h
   · subst U;simp only [List.flatten_cons,List.length_append];omega
   · have b:=ih h;simp only [List.flatten_cons,List.length_append];omega

theorem generated_cap (S : Tree) (color : Nat→Nat) (r N : Nat)
 (sn:treeNodes S≤N) (o : CoreProgram.Output) (mem:o∈(CoreProgram.generate S color r).outputs) :
 OutputCap N o := by
 have p:=CutRealization.generate_partition_check S color r o mem
 have len: o.partition.flatten.length≤N :=
  by have eq:=(CutRealization.generate_payload_perm S color r o mem).length_eq; have l:=leaves_nodes S;omega
 exact ⟨Nat.le_trans (SourceCoverage.partitionCheck_block_bound _ _ p) (Nat.le_trans (leaves_nodes S) sn),
  fun U h=>Nat.le_trans (block_le_flatten _ U h) len⟩

theorem knownOne_payload (T S : Tree) (A : List Nat) (N : Nat) (sn:treeNodes S≤N)
 (F : List (List Nat)) (h:knownOne T S A=some F) : F.length≤2 ∧ F.flatten.length≤2*N := by
 unfold knownOne at h
 cases ht:restrict A T with
 | none=>simp [ht] at h
 | some t=>cases hs:restrict A S with
   | none=>simp [ht,hs] at h
   | some s=>
     simp only [ht,hs] at h
     cases hp:DepthOne.pretest01 t s with
     | refused=>simp [hp] at h
     | rejected=>simp [hp] at h
     | found c=>cases c with
       | none=>simp [hp] at h
       | some v=>
         have eq:F=DepthOne.forest s (some v):=by simpa only [hp,Option.some.injEq] using h.symm
         subst F
         have caps:=forest_cells s (some v)
         exact ⟨caps.1,Nat.le_trans caps.2 (Nat.mul_le_mul_left 2 (Nat.le_trans (restricted_nodes A S s hs) sn))⟩

theorem entries_cap (q N : Nat) (mode : Mode) (os : List CoreProgram.Output)
 (om:ModeCap N mode) (caps:∀o,o∈os→OutputCap N o) :
 ∀e,e∈entries q mode os→EntryCap N e := by
 intro e hm
 simp only [entries,List.mem_filterMap] at hm
 obtain ⟨o,ho,he⟩:=hm
 split at he
 · have eq:⟨o,mode,q-o.sourceCuts.length-mode.extra⟩=e:=Option.some.inj he
   subst e;exact ⟨caps o ho,om⟩
 · cases he

theorem cheapPlan_cap (S T : Tree) (A B C D : List Nat) (q N : Nat)
 (sn:treeNodes S≤N) (bl:B.length≤N) (cl:C.length≤N)
 (cheap opposite : List CoreProgram.Output)
 (cc:∀o,o∈cheap→OutputCap N o) (oc:∀o,o∈opposite→OutputCap N o) :
 ∀e,e∈cheapPlan S T A B C D q cheap opposite→EntryCap N e := by
 simp only [cheapPlan]
 split
 · cases hk:knownOne T S A with
   | none=>simp
   | some F=>
     have f:=knownOne_payload T S A N sn F hk
     intro e hm;rcases List.mem_append.1 hm with h|h
     · exact entries_cap q N .ordinary cheap True.intro cc e h
     · exact entries_cap q N (.retained A B C F) opposite ⟨bl,cl,f⟩ oc e h
 · intro e hm;rcases List.mem_append.1 hm with h|h
   · exact entries_cap q N .ordinary cheap True.intro cc e h
   · exact entries_cap q N .full opposite True.intro oc e h

theorem reuse_cap (S : Tree) (color : Nat→Nat) (probe : List CoreProgram.Output) (q N : Nat)
 (sn:treeNodes S≤N) (caps:∀o,o∈probe→OutputCap N o) :
 ∀o,o∈reuse S color probe q→OutputCap N o := by
 unfold reuse
 split
 · exact generated_cap S color q N sn
 · exact caps

/-- Actual generators and the actual knownOne return establish every local guard.
 No semantic success, properness or callback payload assumption is required. -/
theorem plan_cap (S T : Tree) (A B C D : List Nat) (q N : Nat)
 (sn:treeNodes S≤N) (al:A.length≤N) (bl:B.length≤N) (cl:C.length≤N) :
 ∀e,e∈(bothBadPlanMeter S T A B C D q).value→EntryCap N e := by
 rw [bothBadPlanMeter_value]
 have a:=generated_cap S (cheapColor A B D) 3 N sn
 have b:=generated_cap S (cheapColor B A D) 3 N sn
 have x:=generated_cap S (cheapColor A B D) q N sn
 have y:=generated_cap S (cheapColor B A D) q N sn
 have ra:=reuse_cap S (cheapColor A B D) _ q N sn a
 have rb:=reuse_cap S (cheapColor B A D) _ q N sn b
 by_cases low:q<3
 · simp only [plan,low,ite_true,List.not_mem_nil,false_implies,implies_true]
 · by_cases ha:(CoreProgram.generate S (cheapColor A B D) 3).outputs.isEmpty=true
   · by_cases hb:(CoreProgram.generate S (cheapColor B A D) 3).outputs.isEmpty=true
     · simp only [plan,fourProbe,low,ha,hb,ite_false,ite_true]
       apply entries_cap q N .full _ True.intro
       intro o hm;exact (List.mem_append.1 hm).elim (x o) (y o)
     · simp only [plan,fourProbe,low,ha,hb,ite_false,ite_true]
       exact cheapPlan_cap S T B A C D q N sn al cl _ _ b ra
   · simp only [plan,fourProbe,low,ha,ite_false]
     exact cheapPlan_cap S T A B C D q N sn bl cl _ _ a rb
end OrdinaryDispatch.Hard2SourceWork.LocalDispatchEnvelope
