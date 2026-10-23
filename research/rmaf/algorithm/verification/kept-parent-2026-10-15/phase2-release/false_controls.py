"""Strict intended false-proposition rejections with source-bound clean twins."""
from pathlib import Path
import json,sys
sys.dont_write_bytecode=True
import rebuild as R

def main():
 H=R.helper();prefix='''import FreshConsumer
namespace NonauthorFalseTwins
open RMAF Universal233 CoreProgram KeptParent

def clade : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def crossed : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.leaf 4)
def color : Nat → Nat := keepColor [0,1] [2] (fun _ => 7)
def crossColor : Nat → Nat := keepColor [0,2] [1,3] (fun _ => 0)
def hasA (o : Output) : Bool := o.partition.any (fun b => b.all ([0,2] : List Nat).contains && ([0,2] : List Nat).all b.contains)
def raw := (generate crossed crossColor 3).outputs
'''
 cases=[
 ('SourceGuard','pairwiseEmbeddings crossed [[0,2],[1,3],[4]] = false','pairwiseEmbeddings crossed [[0,2],[1,3],[4]] = true'),
 ('AllOutputs','raw.all hasA = false','raw.all hasA = true'),
 ('BudgetPrune','(generate clade color 1).outputs = []','(generate clade color 1).outputs.length = 1'),
 ('LargeBTag','color 2 = 22','color 2 = 1'),
 ('MissingOccurrence','raw.length = 2','raw.length = 1'),
 ('DuplicateOccurrence','(raw ++ raw).length = 4','(raw ++ raw).length = 2'),
 ('Restriction','restrict [0,1] clade = some (.node (.leaf 0) (.leaf 1))','restrict [0,1] clade = some (.leaf 0)'),
 ('MalformedLabels','partitionCheck (leaves clade) [[0,1,1],[2],[3]] = false','partitionCheck (leaves clade) [[0,1,1],[2],[3]] = true'),
 ('BadLocalEdge','(⟨[[0],[1,2]],[[false]]⟩ : Output) ∉ (generate NonauthorKeptConsumer.localS NonauthorKeptConsumer.localColor 1).outputs','(⟨[[0],[1,2]],[[false]]⟩ : Output) ∈ (generate NonauthorKeptConsumer.localS NonauthorKeptConsumer.localColor 1).outputs'),
 ('OriginalNonhomeomorphism','restrictionAgrees NonauthorKeptConsumer.S NonauthorKeptConsumer.T NonauthorKeptConsumer.A = false','restrictionAgrees NonauthorKeptConsumer.S NonauthorKeptConsumer.T NonauthorKeptConsumer.A = true')]
 twin=prefix+'\n'.join(f'theorem clean{i} : {yes} := by decide' for i,(_,yes,no) in enumerate(cases))+'\nend NonauthorFalseTwins\n'
 (R.BUILD/'FreshFalseTwins.lean').write_text(twin);t=H.run(R.BUILD,'FreshFalseTwins',['-o','FreshFalseTwins.olean']);assert t['exit']==0,t
 rows=[]
 for name,yes,no in cases:
  module='FreshFalse'+name
  (R.BUILD/(module+'.lean')).write_text(prefix+f'example : {no} := by decide\nend NonauthorFalseTwins\n')
  r=H.run(R.BUILD,module);log=(R.BUILD/(module+'.log')).read_text()
  assert r['exit']!=0 and 'proved that the proposition' in log and 'is false' in log and 'failed to reduce' not in log,(name,r,log)
  rows.append({'id':name,'build':r,'intended_false_proposition':no,'strict_false_diagnostic':True,'source_sha256':R.sha(R.BUILD/(module+'.lean'))})
 manifest=json.loads(R.MANIFEST.read_text());pins={x['path']:x['sha256'] for x in manifest['entries']}
 for name in ['FalseKeptGuard','FalseKeptOverlap','FalseKeptWholeTag','FalseKeptCompleteness','FalseKeptLogic']:
  p=R.AUTHOR/(name+'.lean');assert R.sha(p)==pins[str(p.relative_to(R.ROOT))];(R.BUILD/(name+'.lean')).write_bytes(p.read_bytes())
  r=H.run(R.BUILD,name);log=(R.BUILD/(name+'.log')).read_text()
  assert r['exit']!=0 and 'proved that the proposition' in log and 'is false' in log and 'failed to reduce' not in log,(name,r,log)
  rows.append({'id':name,'build':r,'strict_false_diagnostic':True,'source_sha256':R.sha(p),'author_control_replay':True})
 out={'status':'PASS_STRICT_FALSE_PROPOSITIONS_AND_CLEAN_TWINS','fresh_cases':len(cases),'author_false_replays':5,'false_propositions':len(rows),'clean_twin_build':t,'rows':rows,'all_main_milestones':'OPEN','replication_count_added':0}
 p=R.ROOT/'research/rmaf/results/algorithm-kept-parent-fresh-review-false-controls-v1.json';p.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],len(rows))
if __name__=='__main__':main()
