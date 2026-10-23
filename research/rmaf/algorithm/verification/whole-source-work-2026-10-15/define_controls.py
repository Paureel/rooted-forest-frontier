"""Literal hand-derived expectations; intentionally no instrument import."""
from pathlib import Path
import json
b=Path(__file__).resolve().parent;controls=[]
def z(k):return {'kind':'zero','target':k}
def omit(k):return {'kind':'omit','target':k}
def val(k,x):return {'kind':'value','target':k,'replacement':x}
def meta(k,x):return {'kind':'metadata','target':k,'replacement':x}
def case(id,op,d,v={},counts={},metadata={},plants=None):
 controls.append({'id':id,'op':op,'input':d,'value_fields':v,'counts':counts,'metadata':metadata,'plants':plants or [{'kind':'duplicate_record'},{'kind':'missing_record'}], 'positive_counts':[p['target'] for p in (plants or []) if p['kind'] in ['zero','omit'] and counts.get(p['target'],1)!=0]})
qtree=[[0,1],[2,3]]
base={'target':qtree,'parents':[[0,2],[1],[3]],'active':0,'v':'0'}
case('actual-local-parent-regions-residues','callbacks',{**base,'queries':[0,1,2,3]},
 {'tags':[['local',0],['residue',1],['local',2],['residue',2]],'codes':[0,5,2,6]},
 {'callback.invocations':4,'membership.label_comparisons':15,'leaf.lookup_nodes':9,'region.calls':2},
 {'identifier_max_value':6,'identifier_max_bits':3},[z('membership.label_comparisons'),z('leaf.lookup_nodes'),val('codes.3',2),meta('identifier_max_bits',1)])
case('joint-sum-encoding-collision-trap','callbacks',{**base,'mode':'joint','w':'1','queries':[0,2]},
 {'tags':[['joint',0,2],['joint',2,0]],'codes':[2,8]},
 {'callback.invocations':2,'membership.label_comparisons':7,'leaf.lookup_nodes':9,'region.calls':4},
 {'identifier_max_value':8,'identifier_max_bits':4},[val('tags.1',['joint',0,2]),val('codes.1',2),z('region.calls')])
case('joint-parent-residues-distinct','callbacks',{'target':qtree,'parents':[[0,3],[1],[2]],'active':0,'v':'0','w':'1','mode':'joint','queries':[0,1,2,3]},
 {'tags':[['joint',0,2],['residue',1],['residue',2],['joint',2,1]],'codes':[2,17,18,9]},
 {'callback.invocations':4,'region.calls':4}, {'identifier_max_value':18,'identifier_max_bits':5},[val('codes.2',17),z('callback.encoding_ops'),meta('identifier_max_bits',2)])
case('singleton-root-is-removed-label-three','callbacks',{'target':7,'parents':[[7],[],[]],'active':0,'v':'','queries':[7]},
 {'tags':[['local',3]],'codes':[3]},{'callback.invocations':1,'leaf.lookup_nodes':1,'region.calls':1},{'identifier_max_value':3,'identifier_max_bits':2},[val('codes.0',0),z('leaf.lookup_nodes')])
case('joint-full-coordinate-value-versus-cardinality','callbacks',{'target':0,'parents':[[0],[1],[2]],'active':0,'mode':'joint','v':'','w':'','queries':[0,1,2]},
 {'tags':[['joint',3,3],['residue',1],['residue',2]],'codes':[15,17,18]},
 {'callback.invocations':3,'region.calls':2},{'identifier_max_value':18,'identifier_max_bits':5},[meta('identifier_max_value',3),meta('identifier_max_bits',2),val('codes.2',15)])
case('empty-active-parent-costs-membership','callbacks',{'target':7,'parents':[[],[7],[]],'active':0,'v':'','queries':[7]},
 {'tags':[['residue',1]],'codes':[5]},{'callback.invocations':1,'membership.label_comparisons':1,'leaf.lookup_nodes':0,'region.calls':0},{},[z('membership.label_comparisons'),val('tags.0',['local',0])])
case('overlapping-parent-invalid-not-first-owner','callbacks',{'target':0,'parents':[[0],[0],[]],'active':0,'queries':[0]},
 {'tags':[{'invalid':'overlap'}],'codes':[None]},{'callback.invocations':1,'membership.label_comparisons':2,'leaf.lookup_nodes':0},{},[val('tags.0',['local',3]),z('membership.label_comparisons')])
case('missing-parent-invalid-not-default-residue','callbacks',{'target':[0,1],'parents':[[0],[],[]],'active':0,'queries':[1]},
 {'tags':[{'invalid':'missing-parent'}],'codes':[None]},{'callback.invocations':1,'membership.label_comparisons':1},{},[val('tags.0',['residue',2]),z('membership.label_comparisons')])
case('missing-target-label-lookup-refusal','callbacks',{'target':[0,1],'parents':[[99],[],[]],'active':0,'queries':[99]},
 {'tags':[{'invalid':'missing-target-label'}],'codes':[None]},{'callback.invocations':1,'leaf.lookup_nodes':3},{},[z('leaf.lookup_nodes'),val('tags.0',['local',0])])
case('nonvertex-target-not-silently-original-region','callbacks',{**base,'v':'000','queries':[0]},
 {'tags':[{'invalid':'missing-target-vertex'}],'codes':[None]},{'callback.invocations':1,'region.calls':1},{},[val('tags.0',['local',2]),z('region.calls')])
case('original-address-not-suppressed-path','lookup',{'target':[[0,1],2],'queries':[1,2]},
 {'addresses':['01','1']},{'leaf.lookup_calls':2,'leaf.lookup_nodes':9},{},[val('addresses.0','0'),z('leaf.lookup_nodes')])
case('empty-leaf-hull','hull',{'target':[0,1],'selected':[]},{'hull':[]},{'membership.calls':2,'graph.path_nodes':0},{},[val('hull',['']),omit('membership.calls')])
case('singleton-root-hull','hull',{'target':7,'selected':[7]},{'hull':['']},{'graph.path_nodes':1},{},[val('hull',[]),z('graph.path_nodes')])
case('singleton-leaf-hull-excludes-input-root','hull',{'target':qtree,'selected':[0]},{'hull':['00']},{'graph.path_nodes':1},{},[val('hull',['','0','00']),z('graph.path_nodes')])
case('two-leaf-original-minimal-hull','hull',{'target':qtree,'selected':[0,1]},{'hull':['0','00','01']},{},{},[val('hull',['','0','00','01']),{'kind':'duplicate_record'}])
case('empty-joint-color-set','regions',{'target':qtree,'selected':[],'v':'0','w':'1'},
 {'leaf_addresses':[],'joint':[],'distinct_joint':[],'joint_count':0},{'membership.calls':4,'region.calls':0},{},[val('joint_count',1),omit('membership.calls')])
case('leafless-middle-not-third-joint-region','regions',{'target':qtree,'selected':[0,3],'v':'0','w':'1'},
 {'leaf_addresses':['00','11'],'joint':[[0,2],[2,1]],'joint_codes':[2,9],'distinct_joint':[[0,2],[2,1]],'joint_count':2},
 {'region.calls':4,'dedup.input_cells':2,'dedup.kept_cells':2},{},[val('joint_count',3),val('distinct_joint',[[0,2],[2,2],[2,1]]),z('region.calls')])
case('four-joint-signatures-counted','regions',{'target':qtree,'selected':[0,1,2,3],'v':'0','w':'1'},
 {'joint':[[0,2],[1,2],[2,0],[2,1]],'joint_codes':[2,6,8,9],'joint_count':4},
 {'region.calls':8,'dedup.input_cells':4,'dedup.record_comparisons':6},{},[val('joint_count',3),z('dedup.record_comparisons')])
case('actual-clique-original-overlap-selector','selector',{'target':[[[0,1],2],[[3,4],5]],'parents':[[0,3],[1,4],[2,5]]},
 {'triple_overlap':['','0','1'],'pair_overlap.0':['','0','00','1','10']},{'target.build_nodes':11},{},[val('triple_overlap',[]),z('graph.path_nodes')])
clique=[[['local',1,'v'],['local',2,'v']],[['local',0,'v'],['local',2,'v']],[['local',0,'v'],['local',1,'v']]]
chain=[[['local',1,'v'],['local',2,'w']],[['joint',1,'v','w']],[['local',0,'v'],['local',2,'w']],[['local',0,'v'],['local',1,'w']]]
joint=[[['joint',1,'v','w']],[['local',0,'v'],['local',2,'w']]]
for f,alts in [('clique',clique),('chain',chain),('joint',joint)]:
 case('literal-'+f+'-alternative-identities','schedule',{'family':f},{'alternatives':alts,'calls':len(alts)}, {},{},[val('calls',len(alts)-1),val('alternatives',alts[:-1])])
case('outer-left-raw-duplicates-retained','outer',{'outputs':[['A'],['B'],['A']],'association':'left'},
 {'raw':['A','B','A'],'refusals':[],'dedup':['A','B'],'raw_count':3},
 {'outer.outputs.append_calls':3,'outer.outputs.left_cells':3,'outer.outputs.cell_upper_ops':24,'dedup.input_cells':3,'dedup.record_comparisons':2,'dedup.kept_cells':2},{'cell_multiplier':8},[z('outer.outputs.left_cells'),z('outer.outputs.cell_upper_ops'),val('raw',['A','B']),val('dedup',['A'])])
case('outer-right-four-singletons','outer',{'outputs':[['A'],['B'],['C'],['D']],'association':'right'},
 {'raw':['A','B','C','D'],'dedup':['A','B','C','D'],'raw_count':4},
 {'outer.outputs.append_calls':4,'outer.outputs.left_cells':4,'outer.outputs.cell_upper_ops':32,'dedup.record_comparisons':6},{},[z('outer.outputs.cell_upper_ops'),val('raw',['A','C','D']),z('dedup.record_comparisons')])
case('outer-empty-left-still-has-base-call','outer',{'outputs':[[],[]],'association':'left'},
 {'raw':[],'dedup':[],'raw_count':0},{'outer.outputs.append_calls':2,'outer.outputs.left_cells':0},{},[omit('outer.outputs.append_calls'),{'kind':'duplicate_record'}])
case('outer-refusal-left-cells-not-free','outer',{'outputs':[[],[],[]],'refusals':[['root'],['duplicate'],['entire']],'association':'left'},
 {'raw':[],'refusals':['root','duplicate','entire'],'raw_count':0},
 {'outer.refusals.append_calls':3,'outer.refusals.left_cells':3,'outer.refusals.cell_upper_ops':24},{},[z('outer.refusals.left_cells'),z('outer.refusals.cell_upper_ops'),val('refusals',['root','entire'])])
A={'partition':[[0],[1]],'cuts':['0']};B={'partition':[[1],[0]],'cuts':['0']}
case('literal-dedup-does-not-hide-partition-order','outer',{'outputs':[[A],[B]],'association':'left'},
 {'raw':[A,B],'dedup':[A,B],'raw_count':2},{'dedup.record_comparisons':1,'dedup.kept_cells':2},{},[val('dedup',[A]),z('dedup.record_comparisons')])
basegen={'source':[0,1],'target':[0,1],'parents':[[0,1],[],[]],'active':0,'v':'','budget':1,'association':'left'}
for f,a,copies in [('clique',3,3),('chain',4,6),('joint',2,1)]:
 case('whole-'+f+'-unchanged-budget-calls','generate',{**basegen,'family':f},
 {'raw_count':a,'dedup_count':1,'raw_outputs':[A]*a,'pruned':0,'attempts':a,'trace.0.budget':1,'trace.0.source':[0,1]},
 {'caller.generate_invocations':a,'callback.invocations':2*a,'membership.label_comparisons':3*a,'leaf.lookup_nodes':5*a,'outer.outputs.left_cells':copies,'outer.outputs.cell_upper_ops':8*copies,'dedup.record_comparisons':a-1},
 {'budget_bits':1},[z('callback.invocations'),z('leaf.lookup_nodes'),z('outer.outputs.cell_upper_ops'),val('trace.0.budget',0),val('raw_count',1)])
case('whole-zero-budget-keeps-callback-and-local-work','generate',{**basegen,'family':'clique','budget':0},
 {'raw_count':0,'dedup_count':0,'pruned':3,'attempts':3,'trace.0.budget':0},
 {'caller.generate_invocations':3,'callback.invocations':6,'leaf.lookup_nodes':15,'outer.outputs.append_calls':3},{},[z('callback.invocations'),z('leaf.lookup_nodes'),val('pruned',0),omit('outer.outputs.append_calls')])
case('duplicate-source-refusal-zero-callbacks','generate',{**basegen,'family':'clique','source':[7,7],'target':[7,8],'parents':[[7],[8],[]],'budget':3},
 {'raw_count':0,'refusal_count':3,'raw_refusals':['duplicate original label']*3,'pruned':0,'trace.0.callbacks':0},
 {'caller.generate_invocations':3,'callback.invocations':0,'outer.refusals.left_cells':3,'outer.refusals.cell_upper_ops':24},{},[val('trace.0.callbacks',2),z('outer.refusals.cell_upper_ops'),val('refusal_count',1)])
H=2**128
case('oversized-budget-and-label-encoding-not-erased','generate',{**basegen,'family':'joint','source':[0,H],'target':[0,H],'parents':[[0,H],[],[]],'budget':H},
 {'raw_count':2,'dedup_count':1,'trace.0.budget':H,'trace.0.source':[0,H]},
 {'caller.generate_invocations':2,'callback.invocations':4,'outer.outputs.left_cells':1,'outer.outputs.cell_upper_ops':8},
 {'budget_bits':129,'source_label_bits':129,'target_label_bits':129,'identifier_max_value':1,'identifier_max_bits':1},[meta('budget_bits',1),meta('source_label_bits',1),meta('target_label_bits',1),z('outer.outputs.cell_upper_ops')])
# A literal high-volume outer join tests cells independently of small tree size.
case('outer-long-left-list-not-unit-work','outer',{'outputs':[list(range(16)),[16]],'association':'left'},
 {'raw':list(range(17)),'raw_count':17,'dedup':list(range(17))},
 {'outer.outputs.left_cells':16,'outer.outputs.cell_upper_ops':128,'dedup.record_comparisons':136},{},[z('outer.outputs.left_cells'),z('outer.outputs.cell_upper_ops'),z('dedup.record_comparisons')])
x={'phase':'PRE-CANDIDATE literal expectations; manually expanded source/spec, no instrument outputs','controls':controls,'declared_controls':len(controls),'declared_plants':sum(len(c['plants']) for c in controls),'pilot_ids':['actual-local-parent-regions-residues','original-address-not-suppressed-path','outer-left-raw-duplicates-retained'],'size_pilot_ids':['leafless-middle-not-third-joint-region','actual-clique-original-overlap-selector','whole-chain-unchanged-budget-calls','outer-long-left-list-not-unit-work']}
(b/'CONTROL-PIN.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:v for k,v in x.items() if k!='controls'}))
