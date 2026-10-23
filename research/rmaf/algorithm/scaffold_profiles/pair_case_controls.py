"""One-shot local structural plants; these do not assert hard-cherry admission."""
from pathlib import Path
import sys,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
import case_selector as S
D=S.D;C=D.C;O=D.O;R=D.ROOT
out=R/'research/rmaf/results/algorithm-scaffold-profiles-both-bad-controls-v1.json'
if out.exists():raise FileExistsError(out)
def control(a1,a2,b1,b2,asrc,bsrc,kind):
 t=(((a1,b1),(a2,b2)),(8,9));A=O.Tree(asrc);B=O.Tree(bsrc);target=O.Tree(t)
 assert target.clusters(A.labels)!=A.clusters(A.labels) and target.clusters(B.labels)!=B.clusters(B.labels)
 sel=S.select(t,A.labels,B.labels);assert sel['case']=='mutually-clear-binary'
 colors=[{x:i for i,g in enumerate(groups) for x in g} for groups in sel['color_groups']]
 ra,rb=C.generate(asrc,colors[0]),C.generate(bsrc,colors[1]);assert [x['cost'] for x in ra['raw_cores']]==[1]
 assert [x['cost'] for x in rb['raw_cores']]==[2,2]
 rows=[]
 if kind=='bad-sector':
  e=ra['raw_cores'][0];forest=[bsrc,(8,9)]+[A.restriction(p) for p in e['partition']]
  cnt=D.continuation(t,forest);assert len(cnt['queries'])==1 and cnt['queries'][0]['total_loss']==1
  assert cnt['relative_query_mass']==str(1/D.c)
  rows.append({'A_core':e,'continuation':cnt})
 else:
  apart=ra['raw_cores'][0]['partition'];cut=D.matching_cuts(asrc,apart);assert len(cut)==1
  assert D.local_depth1(target.restriction(A.labels),asrc)['value']==1
  for e in rb['raw_cores']:
   actual,empty=B.cut_blocks(e['cuts']);assert not empty and D.canon(actual)==D.canon(e['partition'])
   forest=[asrc,(8,9)]+[B.restriction(p) for p in e['partition']]
   cnt=D.continuation(t,forest);assert cnt['one_unit_progress'] and cnt['queries']
   assert all(q['other_parent_loss']>=1 for q in cnt['queries'])
   tagged_B=[['B',v] for _,v in e['cuts']];tagged_A=[['A',v] for _,v in cut]
   assert all(a!=b for a in tagged_A for b in tagged_B)
   rows.append({'B_core':e,'actual_A_completion_cut':cut,'distinct_parent_paid_cuts':tagged_B+tagged_A,'continuation':cnt})
 return {'case':kind,'target':t,'source_A':asrc,'source_B':bsrc,'selector':sel,'rows':rows}
rows=[control(((0,1),2),3,(4,5),(6,7),((0,(1,2)),3),((4,6),(5,7)),'bad-sector'),
      control((0,1),(2,3),(((4,10),(11,12)),5),(6,7),(((0,1),2),3),((((4,11),(10,12)),6),(5,7)),'both-sectors-good')]
out.write_text(json.dumps({'scope':'Executed local mutually-clear structural plants with arbitrary hard homogeneous group; no earlier-rule admission claim','controls':rows},indent=2)+'\n')
print(json.dumps({'cases':[x['case'] for x in rows],'emissions':[len(x['rows']) for x in rows],'losses':[[[q['total_loss'] for q in y['continuation']['queries']] for y in x['rows']] for x in rows],'out':str(out)}))
