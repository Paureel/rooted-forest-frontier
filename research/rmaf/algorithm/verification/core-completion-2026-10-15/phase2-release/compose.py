"""Copy-only namespace adapter; original frozen theorem bodies are unchanged."""
import json
from pathlib import Path
from rebuild import ROOT,HERE,digest,run,audit_text,parse_audit

CONSUMER='''import ValidPartition
import RationalMass
namespace FreshCompletionReview
open RMAF Universal233 CoreProgram

theorem distinctColorCounts (t : Tree) (color : Nat → Nat) :
    CutRealization.colorCount t color =
      (SourceCoverage.dedupNat ((leaves t).map color)).length := by
  unfold CutRealization.colorCount
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup (CutRealization.color_dedup_nodup _)
    (SourceCoverage.dedupNat_nodup _)).mpr
  intro x
  simp only [List.mem_eraseDups,SourceCoverage.mem_dedupNat]

theorem every_actual_output (t : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate t color q).outputs) :
    CutRealization.RealizedOutput t o ∧ partitionCheck (leaves t) o.partition = true ∧
    (∀ b, b ∈ o.partition → VertexGeometry.LabelMonochromatic color b) ∧
    (SourceCoverage.dedupNat ((leaves t).map color)).length - 1 ≤ o.sourceCuts.length ∧
    o.sourceCuts.length ≤ min q ((leaves t).length - 1) := by
  refine ⟨CutRealization.generate_original_realization t color q o ho,
    CutRealization.generate_partition_check t color q o ho,
    CutRealization.generate_monochromatic t color q o ho,?_,
    SourceCoverage.generate_output_cap t color q o ho⟩
  rw [←distinctColorCounts]
  exact CutRealization.generate_realized_color_cost t color q o ho

/-- Nonauthor consuming call: the refinement witness belongs to the same
literal output list whose ALL members have actual original cuts and whose
RAW list mass is bounded. No runtime, target-tree or solver assertion. -/
theorem completed_source_consumer (t : Tree) (bs : List (List Nat))
    (color : Nat → Nat) (q : Nat)
    (hn : (leaves t).Nodup)
    (hp : partitionCheck (leaves t) bs = true)
    (he : pairwiseEmbeddings t bs = true)
    (hm : ∀ b, b ∈ bs → VertexGeometry.LabelMonochromatic color b)
    (hq : bs.length - 1 ≤ q) (c : Rat) (hc : 2 ≤ c) :
    (∃ o, o ∈ (generate t color q).outputs ∧
      SourceCoverage.RefinesBlocks bs o.partition ∧
      CutRealization.RealizedOutput t o ∧
      partitionCheck (leaves t) o.partition = true ∧
      (∀ b, b ∈ o.partition → VertexGeometry.LabelMonochromatic color b) ∧
      (SourceCoverage.dedupNat ((leaves t).map color)).length - 1 ≤ o.sourceCuts.length ∧
      o.sourceCuts.length ≤ min q ((leaves t).length - 1)) ∧
    SourceCoverage.rawQMass c (generate t color q).outputs ≤
      c ^ (1 - ((SourceCoverage.dedupNat ((leaves t).map color)).length : Int)) := by
  constructor
  · obtain ⟨o,ho,href,hpaid⟩ :=
      SourceCoverage.generate_partition_coverage_paid t bs color hn hp he hm q hq
    exact ⟨o,ho,href,every_actual_output t color q o ho⟩
  · exact SourceCoverage.generate_rawQ_mass t color q c hc

example (t : Tree) (color : Nat → Nat) (q : Nat) :
    SourceCoverage.rawQMass (233/100) (generate t color q).outputs ≤
      (233/100 : Rat) ^ (1 - ((SourceCoverage.dedupNat ((leaves t).map color)).length : Int)) :=
  SourceCoverage.generate_rawQ_mass t color q (233/100) (by decide +kernel)
end FreshCompletionReview
'''

def main():
    dest=HERE/'joint-copy';dest.mkdir(exist_ok=False)
    rows=[];mods=[];mapping=[]
    for arm in ['source','cut']:
        r=json.loads((ROOT/f'research/rmaf/results/algorithm-core-completion-fresh-review-{arm}-rebuild-v1.json').read_text())
        for s in r['sources']:
            old=s['module'];new='CutCoverage' if arm=='cut' and old=='Coverage' else old
            data=(ROOT/s['copy']).read_bytes()
            assert digest(ROOT/s['copy'])==s['sha256']
            if arm=='cut' and old=='InitialCoverage':
                assert data.startswith(b'import Coverage\n')
                changed=data.replace(b'import Coverage\n',b'import CutCoverage\n',1)
                assert changed.split(b'\n',1)[1]==data.split(b'\n',1)[1]
            else: changed=data
            path=dest/(new+'.lean')
            if path.exists():
                assert path.read_bytes()==changed,(arm,old,'shared-source mismatch')
                continue
            path.write_bytes(changed);mods.append(new)
            entry={**s,'arm':arm,'mapped_module':new,'mapped_path':str(path.relative_to(ROOT)),
              'mapped_sha256':digest(path),'body_unchanged':changed.split(b'\n',1)[1]==data.split(b'\n',1)[1],
              'whole_source_unchanged':changed==data}
            rows.append(entry)
            if old!=new or data!=changed:mapping.append(entry)
    (dest/'NonauthorConsumer.lean').write_text(CONSUMER)
    result={'mapping':mapping,'sources':rows,'builds':[],'namespace_adapter_only':True,
      'frozen_files_mutated':False,'all_theorem_bodies_unchanged':all(r['body_unchanged'] for r in rows),
      'consumer_sha256':digest(dest/'NonauthorConsumer.lean')}
    out=ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-joint-v1.json'
    for m in mods+['NonauthorConsumer']:
        b=run(dest,m,['-o',m+'.olean']);result['builds'].append(b)
        out.write_text(json.dumps(result,indent=2)+'\n');print(m,b['exit'],flush=True)
        if b['exit']:raise SystemExit(1)
    finish(dest,mods,result,out)

def finish(dest,mods,result,out):
    (dest/'JointAudit.lean').write_text(audit_text(mods+['NonauthorConsumer'],
      'NonauthorConsumer\nimport Controls\nimport CutControls'))
    b=run(dest,'JointAudit');result['builds'].append(b);assert b['exit']==0,b
    result['audit']=parse_audit(dest/'JointAudit.log',mods+['NonauthorConsumer']);assert not result['audit']['forbidden']
    # Reconcile against each independently rebuilt source package, adjusting
    # only the module origin/private prefix forced by the documented rename.
    actual={(r['module'],r['name']) for r in result['audit']['rows']}
    collision=json.loads((ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-origin-collision-v1.json').read_text())
    assert collision['exact_raw_Expr_type_and_proof_body_identical']
    adopted=[]
    for arm in ['source','cut']:
        old=json.loads((ROOT/f'research/rmaf/results/algorithm-core-completion-fresh-review-{arm}-rebuild-v1.json').read_text())
        expected=set()
        for r in old['audit']['rows']:
            m,n=r['module'],r['name']
            if arm=='cut' and m=='Coverage':m='CutCoverage';n=n.replace('_private.Coverage.','_private.CutCoverage.')
            expected.add((m,n))
        for m,n in expected-actual:
            # The one lazily generated equation declaration is present in both
            # isolated stacks, with identical raw Expr type and proof bytes.
            # The joint importer adopts the cut stack's originating module.
            assert arm=='source' and m=='Entrypoint' and n==collision['declaration']
            assert ('InitialCoverage',n) in actual
            adopted.append({'arm':arm,'name':n,'isolated_origin':m,'joint_origin':'InitialCoverage',
              'raw_type_proof_sha256':collision['reports'][0]['type_and_value_sha256']})
    result['generated_declaration_origin_adoptions']=adopted
    result['complete_origin_reconciliation']=True
    result['olean_hashes']={m:digest(dest/(m+'.olean')) for m in mods+['NonauthorConsumer']}
    result['status']='PASS_SCOPED_JOINT_CONSUMER'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],result['audit']['total'],result['audit']['axiom_union'])

if __name__=='__main__':main()
