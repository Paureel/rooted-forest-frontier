#!/usr/bin/env python3
"""Supplemental post-release corruption checks of the exact readout comparator.

These controls do not acquire pre-candidate preregistration credit. The tested
function is extracted from the retained actual_readout.py source without running
its compilation driver. Clean and corrupted copies use the identical function.
"""
import ast,copy,hashlib,importlib.util,itertools,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('own_frozen',HERE/'frozen-readiness-v1/independent_paircase.py')
m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
body=ast.parse((HERE/'actual_readout.py').read_text())
node=next(n for n in body.body if isinstance(n,ast.FunctionDef) and n.name=='verify_tree')
environment={'itertools':itertools,'m':m}
exec(compile(ast.Module(body=[node],type_ignores=[]),'<retained-exact-verify_tree>','exec'),environment)
verify=environment['verify_tree']
actual=json.loads((HERE/'isolated-review-v1/joint/Fixture0-actual.json').read_text())['S']
tree=m.Original([[1,2],[3,4]])
clean=verify(actual,tree)
rows=[]
def check(name,mutate):
    corrupt=copy.deepcopy(actual);mutate(corrupt)
    caught=False
    try:verify(corrupt,tree)
    except AssertionError:caught=True
    rows.append({'corruption':name,'caught':caught})
    assert caught,name
def choice(d,a,b):return next(r for r in d['choices'] if r['A']==a and r['B']==b)
def hull(d,a):return next(r for r in d['hulls'] if r['selection']==a)
check('missing_selection_denominator',lambda d:d['hulls'].pop())
check('duplicate_selection',lambda d:d['hulls'].append(copy.deepcopy(d['hulls'][0])))
check('missing_color_assignment_denominator',lambda d:d['choices'].pop())
check('original_hull_extra_address',lambda d:hull(d,[1])['hull'].append('111111'))
check('actual_degree_or_region_changed',lambda d:hull(d,[1,3])['regions_degree'][0].__setitem__(1,3))
check('missing_eligible_choice',lambda d:choice(d,[1,3],[2,4]).__setitem__('choice',None))
check('false_choice_outside_guard',lambda d:choice(d,[],[]).__setitem__('choice',{'kind':'vertex','v':''}))
def reverse(d):
    row=choice(d,[1,3],[2,4]);v=row['choice'];assert v['kind']=='edge'
    row['choice']={'kind':'edge','u':v['v'],'v':v['u']}
check('reversed_original_edge',reverse)
out={'verdict':'CLEAN-TWIN-AND-8-READOUT-CORRUPTIONS-CHECKED','clean_counts':clean,'corruptions':rows,
     'source_sha256':hashlib.sha256((HERE/'actual_readout.py').read_bytes()).hexdigest(),
     'provenance':'Supplemental post-release detector controls. No initial preregistration credit; exact retained comparator function tested.'}
path=HERE.parents[2]/'results/algorithm-pair-case-fresh-review-readout-detectors-v1.json'
path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'corruption_denominator':len(rows),'caught':sum(r['caught'] for r in rows),'verdict':out['verdict']}))
