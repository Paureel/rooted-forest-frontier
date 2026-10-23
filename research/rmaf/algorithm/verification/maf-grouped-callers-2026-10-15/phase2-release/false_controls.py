"""Strict finite false propositions, source-bound clean twins, no native decide."""
import json,sys
sys.dont_write_bytecode=True
import rebuild as R
from readout import tree,trees,opt,lit,E

def main():
 H=R.helper();allrows=[];twins=[]
 for arm in ('maf','groups'):
  b=R.HERE/('isolated-'+arm)
  if arm=='maf':
   prefix='import FreshConsumer\nopen RMAF Universal233 MafScheduler\n'
   cases=[('EarlyPrune','calls T1 S1 callback1 3 [[0,1,2,3],[4,5,6,7]]=[]','calls T1 S1 callback1 3 [[0,1,2,3],[4,5,6,7]]=[2,2]'),('OriginalCharge','((solveDisjoint T0 S0 callback0 4 [[0,1,2,3],[4,5,6,7]]).getD []).length-1=5','((solveDisjoint T0 S0 callback0 4 [[0,1,2,3],[4,5,6,7]]).getD []).length-1=4'),('StoredOne','calls T7 S7 callback7 3 [[0,1,2],[3,4,5,6]]=[2]','calls T7 S7 callback7 3 [[0,1,2],[3,4,5,6]]=[3]'),('SoleHard','calls T10 S10 callback10 2 [[0,1,2,3]]=[2]','calls T10 S10 callback10 2 [[0,1,2,3]]=[1]'),('OmittedCall','(calls T0 S0 callback0 4 [[0,1,2,3],[4,5,6,7]]).length=2','(calls T0 S0 callback0 4 [[0,1,2,3],[4,5,6,7]]).length=1'),('DuplicatedCall','(calls T0 S0 callback0 4 [[0,1,2,3],[4,5,6,7]]).length=2','(calls T0 S0 callback0 4 [[0,1,2,3],[4,5,6,7]]).length=3'),('FailedStillPaid','calls T5 S5 callback5 4 [[0,1,2,3],[4,5,6,7]]=[2]','calls T5 S5 callback5 4 [[0,1,2,3],[4,5,6,7]]=[]'),('JointBudget','solveDisjoint T6 S6 callback6 5 [[0,1,2,3],[4,5,6,7]]=none','(solveDisjoint T6 S6 callback6 5 [[0,1,2,3],[4,5,6,7]]).isSome=true'),('AbsentBlock','prepare T0 S0 [[0,1,99],[2,3,4,5,6,7]]=none','(prepare T0 S0 [[0,1,99],[2,3,4,5,6,7]]).isSome=true'),('ForgedAgreement','agreement T0 S0 [[0,1,2,3],[4,5,6,7]]=false','agreement T0 S0 [[0,1,2,3],[4,5,6,7]]=true')]
   author='MafFalseControls';source='maf_scheduler/MafFalseControls.lean';author_count=4
  else:
   prefix='import FreshConsumer\nopen RMAF ForestState ForestGroups\n'
   G={c['id']:c for c in E['grouped_cases']};root=G['root-overlapping-B'];un=G['missing-whole-source-ownership'];hulls=G['whole-group-hulls-overlap-only']
   gT=opt(root['target']);ss=trees(root['sources']);F=lit(root['F']);unArgs=f'{opt(un["target"])} {trees(un["sources"])} {lit(un["Q"])}';hArgs=f'{opt(hulls["target"])} {trees(hulls["sources"])} {lit(hulls["Q"])}'
   cases=[('RootCost',f'additionalCost {ss} {F}=3',f'additionalCost {ss} {F}=2'),('WithinOverlap','disjointVertices (minimalVertices [3,5] NonauthorGroupedConsumer.T) (minimalVertices [4,6] NonauthorGroupedConsumer.T)=false','disjointVertices (minimalVertices [3,5] NonauthorGroupedConsumer.T) (minimalVertices [4,6] NonauthorGroupedConsumer.T)=true'),('FreeWholeB','agrees (some (.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 5) (.leaf 6)))) [.node (.leaf 3) (.leaf 5),.node (.leaf 4) (.leaf 6)] [[3,4,5,6]]=false','agrees (some (.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 5) (.leaf 6)))) [.node (.leaf 3) (.leaf 5),.node (.leaf 4) (.leaf 6)] [[3,4,5,6]]=true'),('UnownedCrossReference',f'crossBool {unArgs}=true',f'crossBool {unArgs}=false'),('UnownedSource',f'ownsBool {trees(un["sources"])} {lit(un["Q"])}=false',f'ownsBool {trees(un["sources"])} {lit(un["Q"])}=true'),('WholeGroupOverguard',f'crossBool {hArgs}=true',f'crossBool {hArgs}=false'),('WholeGroupHulls','pairwiseEmbeddings (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,2],[1,3]]=false','pairwiseEmbeddings (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,2],[1,3]]=true'),('CheaperB','additionalCost [NonauthorGroupedConsumer.b1,NonauthorGroupedConsumer.b2] [[3],[5],[4,6]]=1','additionalCost [NonauthorGroupedConsumer.b1,NonauthorGroupedConsumer.b2] [[3],[5],[4,6]]=2'),('NoneNonempty','proper none [Tree.leaf 7]=false','proper none [Tree.leaf 7]=true'),('EmptyGroup','partitionCheck [0,1,2] [[0,1,2],[]]=false','partitionCheck [0,1,2] [[0,1,2],[]]=true')]
   author='FalseGroupControls';source='forest_groups/FalseGroupControls.lean';author_count=3
  (b/'FreshFalseTwins.lean').write_text(prefix+'\n'.join(f'theorem clean{i} : {yes} := by decide' for i,(_,yes,no) in enumerate(cases))+'\n')
  t=H.run(b,'FreshFalseTwins',['-o','FreshFalseTwins.olean']);twins.append({'arm':arm,**t});assert t['exit']==0,t
  for name,yes,no in cases:
   module='FreshFalse'+name;(b/(module+'.lean')).write_text(prefix+f'example : {no} := by decide\n');x=H.run(b,module);log=(b/(module+'.log')).read_text();assert x['exit']!=0 and 'proved that the proposition' in log and 'is false' in log and 'failed to reduce' not in log,(arm,name,x,log)
   allrows.append({'arm':arm,'id':name,'build':x,'strict_false_proposition':True,'source_sha256':R.sha(b/(module+'.lean'))})
  src=R.ROOT/'research/rmaf/algorithm/universal233'/source;(b/(author+'.lean')).write_bytes(src.read_bytes());x=H.run(b,author);log=(b/(author+'.log')).read_text();assert x['exit']!=0 and log.count('proved that the proposition')==author_count and log.count('is false')>=author_count and 'failed to reduce' not in log
  allrows.append({'arm':arm,'id':author,'build':x,'strict_false_propositions':author_count,'source_sha256':R.sha(src),'author_control_replay':True})
 out={'status':'PASS_STRICT_FALSE_PROPOSITIONS_WITH_CLEAN_TWINS','own_false_propositions':20,'author_false_propositions':7,'rows':allrows,'clean_twin_builds':twins,'reference_error_not_retrofitted':True,'all_main_milestones':'OPEN','replication_count_added':0}
 p=R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-false-controls-v1.json';p.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],27)
if __name__=='__main__':main()
