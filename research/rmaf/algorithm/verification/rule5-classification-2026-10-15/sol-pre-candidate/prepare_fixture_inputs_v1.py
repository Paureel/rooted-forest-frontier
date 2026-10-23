#!/usr/bin/env python3
"""One-shot literal mathematical constructions, before any guard/AF evaluation."""
import hashlib
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
core = [[[0,1],5],6]
small_target = [[[2,core],4],3]
small_source = [[[[[0,[2,3]],4],1],6],5]
large_target = [small_target,7]
large_source = [[[[[0,[[2,3],7]],4],1],6],5]
bad_source = [[[5,[7,8]],9],6]
bad_target = [[[7,[5,6]],9],8]
outside_target = [[0,1],[[[2,bad_target],4],3]]
outside_source = [[[[0,bad_source],4],1],[2,3]]
cases = [
 {'id':'large8','target':large_target,'source':large_source,'a':0,'b':1,'p':2,'q':3,
  'expected_admitted':True,'expected_prefix':'large','good_flags':[True,True,False],
  'original_cuts':[[0,0,0,0,1],[0,0,0,1]],
  'partition':[[2,3,7],[4],[0,1,6,5]],
  'hard_source_forest':[[[2,3],7],4,[[[0,1],6],5]],
  'target_attachments':[[0,0,0,1],[0,0,1]],
  'source_cherry_parent':[0,0,0,0,1,0],
  'terminal_arcs':{'a':[0,0,0,0,0],'b':[0,0,1],'p':[0,0,0,0,1,0,0],'q':[0,0,0,0,1,0,1]},
  'raw_costs':[2]},
 {'id':'sizeTwo7','target':small_target,'source':small_source,'a':0,'b':1,'p':2,'q':3,
  'expected_admitted':True,'expected_prefix':'sizeTwo','good_flags':[True,True,False],
  'original_cuts':[[0,0,0,0,1],[0,0,0,1]],
  'partition':[[2,3],[4],[0,1,6,5]],
  'hard_source_forest':[[2,3],4,[[[0,1],6],5]],
  'target_attachments':[[0,0,1],[0,1]],
  'source_cherry_parent':[0,0,0,0,1],
  'terminal_arcs':{'a':[0,0,0,0,0],'b':[0,0,1],'p':[0,0,0,0,1,0],'q':[0,0,0,0,1,1]},
  'raw_costs':[2,2,2,2,2]},
 {'id':'outside10','target':outside_target,'source':outside_source,'a':0,'b':1,'p':2,'q':3,
  'expected_admitted':True,'expected_prefix':'outside','good_flags':[False,True,True],
  'original_cuts':[[0,0,0,1],[0,0,1]],
  'partition':[[5,7,8,9,6],[4],[0,1,2,3]],
  'hard_source_forest':[bad_source,4,[[0,1],[2,3]]],
  'target_attachments':[[1,0,0,1],[1,0,1]],
  'source_cherry_parent':[1],
  'terminal_arcs':{'a':[0,0,0,0],'b':[0,1],'p':[1,0],'q':[1,1]},
  'raw_costs':[2,2,2,2,2]},
]
controls = {
 'large_crossing':{'case':'large8','F':[[0,2,4],[1],[3],[5],[6],[7]],
   'split':[[0],[2],[4],[1],[3],[5],[6],[7]],
   'G':[[2,3,7],[4],[0],[1],[5],[6]],'split_added':2,'regroup_saved':2,'net_added':0},
 'large_no_crossing':{'case':'large8','F':[[0,4],[1],[2],[3],[5],[6],[7]],
   'G':[[2,3,7],[4],[0],[1],[5],[6]],'split_added':1,'regroup_saved':2,'net_added':-1},
 'false_strict_exchange':{'case':'large8','F':[[0,2],[1],[3],[4],[5],[6],[7]],
   'G':[[2,3,7],[4],[0,1,5],[6]],'F_blocks':7,'common_refinement_minimum_blocks':8},
 'false_topology':{'case':'sizeTwo7','F':[[2,3],[4],[0,1,5,6]]},
 'false_embedding':{'case':'sizeTwo7','F':[[0,2],[1,3],[4],[5],[6]]},
 'false_child_ownership':{'case':'sizeTwo7','F':[[0,2],[1],[3],[4],[5],[6]],'original_agreement':True,'hard_child_agreement':False},
 'mass_at_2':{'one_cost2':'1/4','five_cost2':'5/4'},
 'raw_list_false_twins':['missing_occurrence','deduplicated_costs','failed_child_dropped','unpaid_pair','wrong_component_offset','own_minimum_discount'],
 'original_cut_false_twins':['root_cut','duplicate_cut','nonexistent_local_address','leafless_internal_component','wrong_original_topology','wrong_embedding','foreign_child_owner'],
}
plants = {
 'three_leaf':{'target':[[0,1],2],'source':[[0,2],1],
     'AF':[[[0,1],[2]],[[0,2],[1]],[[0],[1,2]],[[0],[1],[2]]],'minimum':1},
 'same_cherry':{'target':[0,1],'source':[1,0],'AF':[[[0,1]],[[0],[1]]],'minimum':0},
}
data = {'context':'PRE-CANDIDATE literal constructions; no author fixture inputs',
 'cases':cases,'controls':controls,'reference_plants':plants,
 'fixed_bank_plan':{'baseline_pairs':3,'role_exchanges':3,
  'root_and_selected_cherry_orders_per_baseline':16,'arbitrary_Nat_relabels':3,
  'whole_tree_mirrors':3,'boundary_controls':'named improper/no-eligible/empty-materialization controls'},
 'reference_route':'original-edge subsets + union-find components + canonical rooted shape; no BFS/clade imports',
 'BFS_comparator_route':'pinned own original-vertex BFS + set partitions + clade sets',
 'extra_replication_credit':0,
}
target=HERE/'FIXTURE-INPUTS-v1.json'
assert not target.exists()
target.write_text(json.dumps(data,indent=2)+'\n')
target.chmod(0o444)
pin={'path':target.name,'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'candidate_contact':False}
(HERE/'FIXTURE-INPUTS-PIN-v1.json').write_text(json.dumps(pin,indent=2)+'\n')
(HERE/'FIXTURE-INPUTS-PIN-v1.json').chmod(0o444)
print(json.dumps({'constructed_pairs':3,'candidate_contact':False,'input_sha256':pin['sha256']}))
