#!/usr/bin/env python3
"""One-shot literal preregistration; does not execute the graph or Lean instruments."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent.parent
def save(n,v): (P/n).write_text(json.dumps(v,indent=2)+'\n')
B=[[[5,7],9],[[6,8],10]]; Bt=[[5,6],[7,8]]; C=[11,12]
good={'id':'hand-good-A-overlapping-Bpieces','S':[[[[1,2],3],B],C],
 'T':[[[1,Bt],[[2,3],[9,10]]],C],'P':[[1,2,3],[5,6,7,8,9,10],[11,12]],'edge':'00','cheap':'A',
 'expected_sectors':[[1],[2,3],[5,6,7,8],[9,10]],'expected_sector_good':[True,True,False,True],
 'expected_costs':{'A':[3],'B':[4,4]},'expected_probe':{'A':[3],'B':[]},
 'cheap_partition':[[5,7,9,6,8,10],[2,3],[1],[11,12]],'cheap_cuts':['01','00','0000'],
 'opposite_partitions':[[[6,8],[5,7],[11,12],[1,2,3],[9,10]],[[10],[9],[11,12],[1,2,3],[5,7,6,8]]],
 'opposite_cuts':[['0110','0100','1','00'],['0111','0101','1','00']],
 'opposite_within_other_overlap':[True,False],
 'local':{'S':[[1,2],3],'T':[1,[2,3]],'minimum':1,'partition_denominator':5,
          'all_valid_one_edges':['0','1','00','01'],'own_first_certificate':['0'],
          'cheap_sector_certificate':[[1],[2,3]],'capped_cost2_certificate':['00','01']}}
bad={'id':'hand-bad-sector-A-overlapping-Bpieces','S':[[[[[1,2],3],4],B],C],
 'T':[[[[[1,3],2],Bt],[4,[9,10]]],C],'P':[[1,2,3,4],[5,6,7,8,9,10],[11,12]],'edge':'00','cheap':'A',
 'expected_sectors':[[1,2,3],[4],[5,6,7,8],[9,10]],'expected_sector_good':[False,True,False,True],
 'expected_costs':{'A':[3],'B':[4,4]},'expected_probe':{'A':[3],'B':[]},
 'cheap_partition':[[5,7,9,6,8,10],[4],[1,2,3],[11,12]],'cheap_cuts':['01','001','000'],
 'opposite_partitions':[[[6,8],[5,7],[11,12],[1,2,3,4],[9,10]],[[10],[9],[11,12],[1,2,3,4],[5,7,6,8]]],
 'opposite_cuts':[['0110','0100','1','00'],['0111','0101','1','00']],
 'opposite_within_other_overlap':[True,False],'two_bad_blocks':[[1,2,3],[5,6,7,8,9,10]]}
fixtures=[good,bad]
for f in [good,bad]:
 z=json.loads(json.dumps(f));z['id']=f['id'].replace('-A-','-B-');z['P']=[f['P'][1],f['P'][0],f['P'][2]];z['cheap']='B'
 z['expected_sectors']=f['expected_sectors'][2:]+f['expected_sectors'][:2]
 z['expected_sector_good']=f['expected_sector_good'][2:]+f['expected_sector_good'][:2]
 z['expected_costs']={'A':[4,4],'B':[3]};z['expected_probe']={'A':[],'B':[3]};fixtures.append(z)
fixtures.append({'id':'reused-two-high-actual-selector','S':[[[[1,3],[2,4]],[[5,7],[6,8]]],9],
 'T':[[[[1,2],[5,6]],[[3,4],[7,8]]],9],'P':[[1,2,3,4],[5,6,7,8],[9]],'edge':'00','cheap':None,
 'expected_sectors':[[1,2],[3,4],[5,6],[7,8]],'expected_sector_good':[True]*4,
 'expected_costs':{'A':[4,4],'B':[4,4]},'expected_probe':{'A':[],'B':[]},
 'raw_partitions':{'A':[[[2],[1],[9],[5,7,6,8],[3,4]],[[4],[3],[9],[5,7,6,8],[1,2]]],
                   'B':[[[6],[5],[9],[1,3,2,4],[7,8]],[[8],[7],[9],[1,3,2,4],[5,6]]]},
 'raw_cuts':{'A':[['0010','0000','1','01'],['0011','0001','1','01']],
             'B':[['0110','0100','1','00'],['0111','0101','1','00']]}})
outside={'id':'reused-source-overlap-outside','S':[[[[[1,[4,6]],[5,7]],2],3],8],
 'T':[[[1,[4,5]],[[2,3],[6,7]]],8],'P':[[1,2,3],[4,5,6,7],[8]],'edge':'00',
 'expected_false_guards':['source_P_disjoint'],'expected_costs':{'A':[3],'B':[5,5,5,5]}}
clear={'id':'hand-C-clearance-corrupt-outside','S':good['S'],
 'T':[[1,[11,Bt]],[[2,3],[12,[9,10]]]],'P':good['P'],'edge':'0','expected_false_guards':['C_clear']}
old=json.loads((P.parents[2]/'pair_case/cheap_high/x0/sol-handoff-v1/payload/sol-fixtures-v1.json').read_text())
save('fixtures-v1.json',{'phase':'PRE-CANDIDATE','frozen_before_new_execution':True,'rational_c':[[2,1],[233,100],[3,1]],
 'fixtures':fixtures,'outside':[outside,clear],'reused_public_false_control':old['fixtures'][-1],
 'public_F':[[1],[2],[3,5],[4],[6],[7]],'public_Fprime':[[1,2],[3],[5],[4],[6],[7]],
 'primitive_controls':old['controls'],'budget_rule':'all q in 0..number_of_labels+2 inclusive; cap n-1',
 'raw_list_rule':'literal call A then B; retain every occurrence and source cut order',
 'malformed_expected':{'duplicate_labels':'reject','missing_label_selector':'none','root_edge':'reject','leaf_edge':'reject','absent_edge':'reject','child_order':'topology invariant, literal addresses transported','suppressed_path':['0','00','000','01']},
 'mutations_expected_rejected':['omitted raw occurrence','duplicated raw occurrence','wrong four-color cardinality','three-color edge','original F refines some literal output','whole bad parent one source cut','different selected edge on swap','target embedding implies target agreement','local cut reused as whole-source cut','positive minimum gives every capped query a unit discount'],
 'no_replication_increment':True,'candidate_contact':False})
save('instrument-freeze-v1.json',{'files':[{'path':str(z.relative_to(P)),'sha256':hashlib.sha256(z.read_bytes()).hexdigest()} for z in sorted((P/'instrument').glob('*.py'))],
 'fixtures_sha256':hashlib.sha256((P/'fixtures-v1.json').read_bytes()).hexdigest(),'execution_not_started':True})
print('Frozen five in-regime expectations, two guard corruptions, public false control and mutation bank; no evaluator execution.')
