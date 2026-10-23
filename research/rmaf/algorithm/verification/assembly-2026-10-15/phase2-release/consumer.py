"""Nonauthor universal adapter and literal frozen-fixture theorem consumers."""
from rebuild import ROOT,HERE,run,digest,audit_text,parse_audit
from readout import C,tree,lit,vertex
import json

PREFIX='''import HardPaid
namespace FreshAssemblyReview
open RMAF Universal233 CoreProgram SourceCoverage VertexGeometry PaidAssembly

def refineBool (F Q : List (List Nat)) : Bool :=
  F.all (fun b => Q.any (fun a => b.all a.contains))

theorem refineBool_sound (F Q : List (List Nat)) (h : refineBool F Q = true) : RefinesBlocks F Q := by
  intro b hb
  have he := List.all_eq_true.mp h b hb
  obtain ⟨a,ha,hs⟩ := List.any_eq_true.mp he
  exact ⟨a,ha,fun x hx => List.contains_iff_mem.mp (List.all_eq_true.mp hs x hx)⟩

theorem reverse_blocks (a b c d : List α) :
    (((a ++ b) ++ c) ++ d).Perm (((d ++ c) ++ b) ++ a) := by
  have h1 := List.perm_append_comm (l₁ := (a ++ b) ++ c) (l₂ := d)
  have h2 := (List.perm_append_comm (l₁ := a ++ b) (l₂ := c)).append_left d
  have h3 := ((List.perm_append_comm (l₁ := a) (l₂ := b)).append_left c).append_left d
  simpa only [List.append_assoc] using h1.trans (h2.trans h3)

def referenceFour (S T : Tree) (A B : List Nat) (v w : RMAF.Vertex) (q : Nat) : List Output :=
  ((WholeSourceMass.wholeOutputs S A B (colorLabel T v) (colorLabel T w) (fun _ => 0) q ++
    WholeSourceMass.wholeOutputs S A B (colorLabel T v) (fun _ => 0) (colorLabel T w) q) ++
    WholeSourceMass.wholeOutputs S A B (fun _ => 0) (WholeSourceMass.jointLabel T v w) (fun _ => 0) q) ++
    WholeSourceMass.wholeOutputs S A B (fun _ => 0) (colorLabel T v) (colorLabel T w) q

/-- Reference order differs; this universal Perm retains EVERY occurrence. -/
theorem actual_four_reference_permutation (S T : Tree) (A B : List Nat)
    (v w : RMAF.Vertex) (q : Nat) :
    (WholeSourceMass.fourChainOutputs S T A B v w q).Perm (referenceFour S T A B v w q) := by
  unfold WholeSourceMass.fourChainOutputs referenceFour
  exact reverse_blocks _ _ _ _

/-- The original fixed cut list is selected before F or its budget. Neither
parent refinement nor an emitted witness is a premise of this consumer. -/
theorem uniform_hard_clique_paid (T S : Tree) (v : RMAF.Vertex)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup)
    (hl : ∀ x, x ∈ leaves S → x ∈ leaves T)
    {z : RMAF.Vertex} {a b : Nat} (hc : CoreGraph.CherryAt T z a b)
    (h2 : (HardParent.pendantOriginal S a b).length = 2)
    (hi : ¬selectedLeaves (leaves T) T v) :
    ∃ p r, HardParent.pendantOriginal S a b = [p,r] ∧
      ∀ F q, agreement T S F = true → F.length-1 ≤ q →
      v ∈ minimalVertices (leftParent S p) T →
      v ∈ minimalVertices (rightParent S r) T →
      v ∈ minimalVertices (rootParent S p r) T →
      ∀ c : Rat, 2 ≤ c →
      Hard2Covered S F a b p r q
        (WholeSourceMass.cliqueOutputs S T (leftParent S p) (rightParent S r) v q)
        (fun o => CliqueClearing T o.partition (leftParent S p) (rightParent S r) (rootParent S p r) v) ∧
      rawQMass c (WholeSourceMass.cliqueOutputs S T (leftParent S p) (rightParent S r) v q) ≤ 3*c^(-4 : Int) := by
  have he := List.eq_getElem_of_length_eq_two (HardParent.pendantOriginal S a b) h2
  refine ⟨_,_,he,?_⟩
  intro F q hf hq hA hB hC c hbase
  exact hard2_clique_paid T S F v q ht hs hl hf hc he hi hA hB hC hq c hbase
'''

def main():
    text=PREFIX;fixture_names=[]
    for j,M in enumerate(C['macros']):
        T,S=tree(M['target']),tree(M['source']);aa,bb,cc=map(lit,M['parents']);v=vertex(M['v']);w=vertex(M['w']) if 'w' in M else None
        text+=f'\ndef target{j} : Tree := {T}\ndef source{j} : Tree := {S}\n'
        TT,SS=f'target{j}',f'source{j}'
        for k,f in enumerate(M['forests']):
            F=lit(f['F']);q=f.get('q',len(f['F'])-1);name=f'fixture_{j}_{k}';fixture_names.append(name)
            function={'clique':'cliqueOutputs','four-chain':'fourChainOutputs','two-joint-diagonal':'diagonalOutputs'}[M['id']]
            clear={'clique':'CliqueClearing','four-chain':'FourClearing','two-joint-diagonal':'DiagonalClearing'}[M['id']]
            paid={'clique':'clique_paid_cover','four-chain':'four_paid_cover','two-joint-diagonal':'diagonal_paid_cover'}[M['id']]
            pos=v+(' '+w if w else '')
            whole=f'(WholeSourceMass.{function} {SS} {TT} {aa} {bb} {pos} {q})'
            bound='3*(233/100 : Rat)^(-4 : Int)' if M['id']=='clique' else '4*(233/100 : Rat)^(-4 : Int)' if M['id']=='four-chain' else '(233/100 : Rat)^(-3 : Int)+(233/100 : Rat)^(-4 : Int)'
            text+=f'''theorem {name} :
    (∃ o, o ∈ {whole} ∧ OutputWitness {SS} [{aa},{bb},{cc}] {F} {q} o ∧
      {clear} {TT} o.partition {aa} {bb} {cc} {pos}) ∧
    rawQMass (233/100) {whole} ≤ {bound} := by
  apply {paid} {TT} {SS} {aa} {bb} {cc} {F} {pos} {q}
  · decide
  · decide
  · intro x hx
    simp only [source{j},target{j},leaves,List.mem_cons,List.not_mem_nil,or_false,List.mem_append] at hx ⊢
    omega
  · decide
  · decide
  · exact refineBool_sound _ _ (by decide)
  · simp [target{j},selectedLeaves,Join]
'''
            if w:text+=f'  · simp [target{j},selectedLeaves,Join]\n'
            for _ in range(3 if M['id']=='clique' else 4):text+='  · decide\n'
            if w:text+='  · decide\n' # actual joint count gate
            text+='  · decide\n  · decide +kernel\n'
    text+='\nend FreshAssemblyReview\n'
    build=HERE/'isolated-completion';(build/'NonauthorConsumer.lean').write_text(text)
    r=run(build,'NonauthorConsumer',['-o','NonauthorConsumer.olean'])
    result={'build':r,'source_sha256':digest(build/'NonauthorConsumer.lean'),
      'universal_consumers':['actual_four_reference_permutation','uniform_hard_clique_paid'],
      'fixture_consumers':fixture_names,'all_main_milestones':'OPEN','replication_count_added':0}
    out=ROOT/'research/rmaf/results/algorithm-assembly-fresh-review-nonauthor-consumer-v1.json'
    out.write_text(json.dumps(result,indent=2)+'\n');assert not r['exit'],r
    result['status']='PASS_NONAUTHOR_UNIVERSAL_AND_LITERAL_CONSUMERS';out.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],len(fixture_names),'frozen forest theorem consumers')

if __name__=='__main__':main()
