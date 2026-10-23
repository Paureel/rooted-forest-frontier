#!/usr/bin/env python3
"""Literal fixture writer only; no ledger, candidate or prior verifier imports."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
rows=[]
def plant(kind,target=None,wrong=None):
    r={'kind':kind}
    if target is not None:r['target']=target
    if wrong is not None:r['wrong']=wrong
    return r
def add(name,op,data,value,counts,plants,metadata=None):
    rows.append({'id':name,'op':op,'input':data,'value_fields':value,
                 'counts':counts,'metadata':metadata or {},'plants':plants})
S=[[0,1],2]; Q=[[0,1],[2,3]]
ID={'kind':'id'}; HOM={'kind':'constant','value':7}
M={'kind':'table','values':[0,0,1]}; ALT={'kind':'table','values':[0,1,0,1]}
def rv(outputs,refusals,visited=0,attempts=0,pruned=0):
    return {'outputs':outputs,'refusals':refusals,'visited':visited,'childAttempts':attempts,'pruned':pruned}

add('empty-left-append-call-still-present','append',{'domain':'literal','left':[],'right':[1,2]},
    {'$':[1,2]},{'append.literal.calls':1,'append.literal.left_cells':0},
    [plant('omit_kind','append.literal.calls'),plant('duplicate_record')])
add('nonempty-left-append-work','append',{'domain':'literal','left':[10,11,12],'right':[20]},
    {'$':[10,11,12,20]},{'append.literal.calls':1,'append.literal.left_cells':3},
    [plant('zero_kind','append.literal.left_cells'),plant('missing_record')])
add('combine-materializes-both-left-lists','combine',
    {'left':{'outputs':['L0','L1','L2'],'refusals':['a','b'],'visited':2,'attempts':4,'pruned':6},
     'right':{'outputs':['R0','R1'],'refusals':['c'],'visited':3,'attempts':5,'pruned':7}},
    rv(['L0','L1','L2','R0','R1'],['a','b','c'],5,9,13),
    {'append.receipt_outputs.calls':1,'append.receipt_outputs.left_cells':3,
     'append.receipt_refusals.calls':1,'append.receipt_refusals.left_cells':2,'counter.add':3},
    [plant('zero_kind','append.receipt_outputs.left_cells'),plant('zero_kind','append.receipt_refusals.left_cells'),
     plant('duplicate_output'),plant('missing_output')])
add('combine-empty-left-lists','combine',
    {'left':{'outputs':[],'refusals':[]},'right':{'outputs':['R'],'refusals':['r']}},
    rv(['R'],['r']),{'append.receipt_outputs.calls':1,'append.receipt_outputs.left_cells':0,
                    'append.receipt_refusals.calls':1,'append.receipt_refusals.left_cells':0,'counter.add':3},
    [plant('zero_kind','append.receipt_outputs.calls'),plant('missing_record')])
add('combine-left-output-length-eight','combine',
    {'left':{'outputs':[0,1,2,3,4,5,6,7],'refusals':[]},'right':{'outputs':[8],'refusals':[]}},
    rv([0,1,2,3,4,5,6,7,8],[]),
    {'append.receipt_outputs.calls':1,'append.receipt_outputs.left_cells':8,'counter.add':3},
    [plant('zero_kind','append.receipt_outputs.left_cells')])
add('combine-left-output-length-sixteen','combine',
    {'left':{'outputs':[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],'refusals':[]},
     'right':{'outputs':[16],'refusals':[]}},
    rv([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],[]),
    {'append.receipt_outputs.calls':1,'append.receipt_outputs.left_cells':16,'counter.add':3},
    [plant('zero_kind','append.receipt_outputs.left_cells'),plant('duplicate_record')])
add('singleton-fromTree-color-oracle','fromTree',{'tree':7,'colors':ID,'oracle_tariff':3},
    {'$':{'root':'','groups':[['',[7],7]]}},
    {'fromTree.visit':1,'oracle.color_calls':1,'oracle.tariff_units':3,'append.origin.calls':0},
    [plant('omit_kind','oracle.color_calls'),plant('metadata','input_label_max_bits',1)],
    {'input_label_max_bits':3})
add('fromTree-three-leaves-original-address-work','fromTree',{'tree':S,'colors':ID,'oracle_tariff':5},
    {'$':{'root':'','groups':[['00',[0],0],['01',[1],1],['1',[2],2]]}},
    {'fromTree.visit':5,'oracle.color_calls':3,'oracle.tariff_units':15,
     'append.origin.calls':4,'append.origin.left_cells':2},
    [plant('omit_kind','oracle.color_calls'),plant('zero_kind','append.origin.left_cells')])
add('fromTree-nonempty-original-prefix','fromTree',{'tree':S,'colors':ID,'prefix':'10'},
    {'$':{'root':'10','groups':[['1000',[0],0],['1001',[1],1],['101',[2],2]]}},
    {'fromTree.visit':5,'oracle.color_calls':3,'append.origin.calls':4,'append.origin.left_cells':10},
    [plant('zero_kind','append.origin.left_cells'),plant('duplicate_record')])
add('normalization-homogeneous-payload-appends','normalize',{'tree':S,'colors':HOM},
    {'$':{'root':'','groups':[['',[0,1,2],7]]}},
    {'normalize.visit':5,'compare.normalize_color':2,'append.normalize_payload.calls':2,
     'append.normalize_payload.left_cells':3,'oracle.color_calls':0},
    [plant('zero_kind','append.normalize_payload.left_cells'),plant('zero_kind','normalize.visit')])
add('normalization-mixed-comparison-still-charged','normalize',{'tree':S,'colors':M},
    {'$':{'root':'','groups':[['0',[0,1],0],['1',[2],1]]}},
    {'normalize.visit':5,'compare.normalize_color':2,'append.normalize_payload.calls':1,
     'append.normalize_payload.left_cells':1},
    [plant('zero_kind','compare.normalize_color'),plant('missing_record')])
add('groups-left-appends','groups',{'tree':S,'colors':ID},
    {'$':[['00',[0],0],['01',[1],1],['1',[2],2]]},
    {'groups.visit':5,'append.groups.calls':2,'append.groups.left_cells':3},
    [plant('zero_kind','append.groups.left_cells')])
add('erase-suppressed-survivor-still-visits','erase',{'tree':S,'colors':ID,'chosen':'00'},
    {'$':{'root':'','groups':[['01',[1],1],['1',[2],2]]}},
    {'erase.visit':5,'compare.origin':5},[plant('zero_kind','erase.visit'),plant('duplicate_record')])
add('erase-original-root-cost','erase',{'tree':S,'colors':ID,'chosen':''},
    {'$':{'root':None,'groups':[]}},{'erase.visit':1,'compare.origin':1},
    [plant('zero_kind','erase.visit')])
add('choose-filter-find-list-work','choose',{'tree':S,'colors':M,'normalize_input':True},
    {'$':{'kind':'one','origins':['0']}},
    {'choose.calls':1,'groups.visit':3,'append.groups.left_cells':1,'choose.all_predicate':2,
     'choose.find_predicate':1,'choose.filter_predicate':2,'choose.filter_kept_cells':1,
     'length.filtered.cells':1,'compare.count':1,'mixedCherry.visit':0},
    [plant('zero_kind','choose.filter_predicate'),plant('missing_record')])
add('choose-refusal-after-real-search','choose',{'tree':Q,'colors':{'kind':'table','values':[0,0,1,1]}},
    {'$':{'kind':'refuse','refusals':['unnormalized homogeneous cherry']}},
    {'choose.calls':1,'groups.visit':7,'append.groups.left_cells':4,'choose.all_predicate':3,
     'choose.find_predicate':4,'choose.filter_predicate':16,'choose.filter_kept_cells':8,
     'length.filtered.cells':8,'mixedCherry.visit':3,'compare.cherry_color':1},
    [plant('zero_kind','choose.all_predicate'),plant('zero_kind','choose.filter_predicate')])
add('attempt-root-refusal-cost','attempt',{'tree':0,'colors':ID,'group':['',[0],0]},
    rv([],['attempt to cut original root'],0,1,0),
    {'attempt.calls':1,'compare.origin':1,'erase.visit':0,'refusal.list_cells':1},
    [plant('zero_kind','attempt.calls'),plant('duplicate_record')])
add('attempt-duplicate-refusal-cost','attempt',
    {'tree':S,'colors':M,'normalize_input':True,'group':['0',[0,1],0],'cuts':['0']},
    rv([],['duplicate original source cut'],0,1,0),
    {'attempt.calls':1,'compare.origin':2,'cuts.contains_calls':1,'cuts.contains_cells':1,
     'erase.visit':0,'refusal.list_cells':1},[plant('zero_kind','compare.origin')])
add('attempt-entire-refusal-cost','attempt',{'tree':2,'prefix':'1','colors':ID,'group':['1',[2],2]},
    rv([],['attempt removed entire current source'],0,1,0),
    {'attempt.calls':1,'compare.origin':2,'cuts.contains_calls':1,'erase.visit':1,
     'prune.callback':0,'refusal.list_cells':1},[plant('zero_kind','erase.visit')])
add('attempt-prune-still-pays-local-erase','attempt',{'tree':[0,1],'colors':ID,'group':['0',[0],0]},
    rv([],[],0,1,1),{'attempt.calls':1,'compare.origin':4,'erase.visit':3,'prune.callback':1,
                    'attempt.cons_cells':2,'counter.add':1},
    [plant('zero_kind','erase.visit'),plant('omit_kind','prune.callback')])
add('run-zero-budget-local-work','run',{'tree':[0,1],'colors':ID,'budget':0},
    rv([],[],1,1,1),{'run.calls':1,'step.calls':1,'normalize.visit':3,'groups.visit':3,
                    'choose.calls':1,'choose.filter_predicate':2,'erase.visit':3,
                    'attempt.calls':1,'prune.callback':1,'counter.add':2,'oracle.color_calls':0},
    [plant('zero_kind','normalize.visit'),plant('omit_kind','prune.callback'),plant('missing_record')])
add('generate-zero-budget-initial-check-and-colors','generate',
    {'tree':[0,1],'colors':ID,'budget':0,'oracle_tariff':7},rv([],[],1,1,1),
    {'generate.calls':1,'leaves.visit':6,'append.leaves.left_cells':2,'initial.nodup_calls':1,
     'initial.nodup_input_cells':2,'compare.label':1,'fromTree.visit':3,'oracle.color_calls':2,
     'oracle.tariff_units':14,'length.initial.cells':2,'budget.min':1,'normalize.visit':3,
     'choose.calls':1,'groups.visit':3,'erase.visit':3,'prune.callback':1},
    [plant('omit_kind','initial.nodup_calls'),plant('omit_kind','oracle.color_calls'),
     plant('zero_kind','normalize.visit')])
add('duplicate-input-pays-check-but-not-colors','generate',{'tree':[7,7],'colors':ID,'budget':3},
    rv([],['duplicate original label']),
    {'generate.calls':1,'leaves.visit':3,'append.leaves.left_cells':1,'initial.nodup_calls':1,
     'initial.nodup_input_cells':2,'compare.label':1,'fromTree.visit':0,'oracle.color_calls':0,
     'budget.min':0,'normalize.visit':0,'refusal.list_cells':1},
    [plant('omit_kind','initial.nodup_calls'),plant('metadata','input_label_max_bits',1)],
    {'input_label_max_bits':3})
PAIR_OUTPUT=[{'partition':[[0],[1]],'cuts':['0']}]
add('generate-finish-materializes-output','generate',{'tree':[0,1],'colors':ID,'budget':9},
    rv(PAIR_OUTPUT,[],2,1,0),
    {'fromTree.visit':3,'oracle.color_calls':2,'run.calls':2,'normalize.visit':4,'groups.visit':5,
     'choose.all_predicate':3,'choose.filter_predicate':2,'erase.visit':3,'prune.callback':0,
     'finish.map_cells':1,'finish.flatmap_group_cells':1,'append.finish_payload.left_cells':1,
     'append.finish_partition.left_cells':1,'finish.output_cells':1},
    [plant('zero_kind','append.finish_payload.left_cells'),plant('omit_kind','oracle.color_calls'),
     plant('metadata','input_budget_bits',1)],{'input_budget_bits':4})
H=1<<128
add('oversized-budget-bit-width-survives-clipping','generate',{'tree':[0,1],'colors':ID,'budget':H},
    rv(PAIR_OUTPUT,[],2,1,0),
    {'fromTree.visit':3,'oracle.color_calls':2,'budget.min':1,'run.calls':2,'normalize.visit':4,
     'prune.callback':0},
    [plant('metadata','input_budget_bits',1),plant('metadata','max_nat_operand_bits',1)],
    {'input_budget_bits':129,'max_nat_operand_bits':129})
add('encoded-labels-and-oracle-tariff','generate',
    {'tree':[0,H],'colors':ID,'budget':1,'oracle_tariff':11},
    rv([{'partition':[[0],[H]],'cuts':['0']}],[],2,1,0),
    {'fromTree.visit':3,'oracle.color_calls':2,'oracle.tariff_units':22,'compare.label':1,
     'compare.normalize_color':1,'run.calls':2},
    [plant('metadata','input_label_max_bits',1),plant('metadata','max_nat_operand_bits',1),
     plant('omit_kind','oracle.tariff_units')],
    {'input_label_max_bits':129,'max_nat_operand_bits':129})
add('two-pruned-children-still-join-receipts','run',{'tree':Q,'colors':ALT,'budget':0},
    rv([],[],1,2,2),
    {'normalize.visit':7,'choose.calls':1,'groups.visit':7,'choose.all_predicate':2,
     'choose.filter_predicate':16,'length.filtered.cells':8,'mixedCherry.visit':3,
     'attempt.calls':2,'erase.visit':14,'compare.origin':16,'prune.callback':2,
     'append.receipt_outputs.calls':1,'append.receipt_outputs.left_cells':0,
     'append.receipt_refusals.calls':1,'counter.add':6},
    [plant('zero_kind','normalize.visit'),plant('zero_kind','append.receipt_outputs.calls')])
add('two-output-source-run-joins-left-output-record','generate',{'tree':Q,'colors':ALT,'budget':2},
    rv([{'partition':[[2],[0],[1,3]],'cuts':['10','00']},
        {'partition':[[3],[1],[0,2]],'cuts':['11','01']}],[],5,4,0),
    {'leaves.visit':14,'append.leaves.left_cells':8,'initial.nodup_calls':1,'compare.label':6,
     'fromTree.visit':7,'oracle.color_calls':4,'append.origin.left_cells':4,
     'run.calls':5,'step.calls':5,'normalize.visit':23,'groups.visit':21,'choose.calls':5,
     'choose.all_predicate':9,'choose.find_predicate':9,'choose.filter_predicate':31,
     'length.filtered.cells':16,'mixedCherry.visit':3,'attempt.calls':4,'erase.visit':24,
     'compare.origin':30,'prune.callback':0,'append.receipt_outputs.left_cells':1,
     'append.receipt_refusals.left_cells':0,'counter.add':10,
     'append.finish_payload.left_cells':4,'append.finish_partition.left_cells':4},
    [plant('zero_kind','append.receipt_outputs.left_cells'),plant('duplicate_output'),
     plant('missing_output'),plant('omit_kind','initial.nodup_calls')])

payload={'scope':'independently constructed literal structural-cost ledgers before candidate content',
         'expected_source':'manual expansion of the four permitted source definitions, no ledger output',
         'declared_controls':len(rows),'declared_plants':sum(len(r['plants']) for r in rows),
         'size_pilot_ids':['fromTree-nonempty-original-prefix','normalization-homogeneous-payload-appends',
                           'generate-zero-budget-initial-check-and-colors','two-output-source-run-joins-left-output-record'],
         'controls':rows,'additional_independent_replications':0}
dest=HERE/'CONTROL-PIN.json';assert not dest.exists()
dest.write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps({'literal_controls_written':len(rows),'plants_written':payload['declared_plants'],
                  'ledger_executed':False}))
