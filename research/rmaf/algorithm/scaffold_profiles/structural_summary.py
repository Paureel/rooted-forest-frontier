"""One-shot DEVELOPMENT summary of owned exact continuation receipts.
No independent verification or broad skeleton census is claimed.
"""
from pathlib import Path
from fractions import Fraction
import json,sys,hashlib
sys.path.insert(0,str(Path(__file__).resolve().parent))
import continuation_probe as D
R=D.ROOT;out=R/'research/rmaf/results/algorithm-scaffold-profiles-structural-summary-v2.json'
if out.exists():raise FileExistsError(out)
# Protected-color control and missing-branch false twin, before contact rows.
q=((0,1),(2,3));color={0:0,1:1,2:0,3:1}
def retained(r,col):
 return [any(any(set(b)=={x for x in col if col[x]==a} for b in e['partition']) for e in r['raw_cores']) for a in sorted(set(col.values()))]
assert retained(D.C.generate(q,color),color)==[True,True]
assert retained(D.C.generate(q,color,omit_first_mixed_right=True),color)!=[True,True]
# Arbitrary hard subtrees are not declared good by the color generator.
source=((0,(1,2)),3);col={0:0,1:0,2:0,3:1}
r=D.C.generate(source,col);assert [e['cost'] for e in r['raw_cores']]==[1]
assert D.local_depth1(((0,1),2),(0,(1,2)))['value']==1
assert not (1+1+2<=2+1) # Three-region exchange cannot pay only one saved A cut.
rows=[];contacts=[]
for name in ('algorithm-scaffold-profiles-continuation-pilot-v1.json','algorithm-scaffold-profiles-continuation-extension-v1.json'):
 p=R/'research/rmaf/results'/name;contacts.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
 for row in json.loads(p.read_text())['rows']:
  t,fs,spans,ov,good,cc=D.geometry(row['initial']['T'],row['initial']['forest_trees'])
  for s in row['selectors']:
   clear=[];protected=[];color_counts=[]
   for b in s['branches']:
    k=b['parent'];other=next(i for i in ov[0] if i!=k);col={int(x):a for x,a in b['colors'].items()}
    groups=[[x for x in col if col[x]==a] for a in sorted(set(col.values()))]
    clear.append(all(not t.span(g)&spans[other] for g in groups));color_counts.append(len(groups))
    if len(groups)==2:
     present=[any(any(set(p)==set(g) for p in e['partition']) for e in b['emissions']) for g in groups]
     assert all(present);protected.append(present)
    else:protected.append(None)
   forced=None
   if color_counts==[2,2] and all(clear) and any(good[b['parent']] for b in s['branches']):
    bad_branch=next((b for b in s['branches'] if not good[b['parent']]),None)
    if bad_branch:
     mass=2/D.c+D.pp.mass(bad_branch['raw_profile'])/D.c**2
     forced={'clear_parent':bad_branch['parent'],'profile':bad_branch['raw_profile'],'conditional_full_mass':str(mass),'passes':mass<1,
       'status':'Conditional on generalized good-parent exchange; not universally formalized here'}
   rows.append({'n':row['n'],'vertex':s['target_vertex'],'region_counts':color_counts,'mutual_clear_directions':clear,
     'whole_color_retained':protected,'profiles':[b['raw_profile'] for b in s['branches']],
     'actual_progress_emissions':s['single_progress_emissions'],'actual_continued_mass':s['continued_full_mass'],
     'conditional_forced_bad_parent_exchange':forced})
result={'scope':'DEVELOPMENT structural summary, not independent certification','controls':{'protected_color_clean_passes':True,'missing_branch_false_twin_caught':True,'hard_group_one_cut_profile_not_terminal':True,'three_region_unit_exchange_false_twin_caught':True},'contacts':contacts,'rows':rows,
 'open':['Universal actual source trace/coverage/cut charge','Shared-vertex/sector selector compression graph proof','Generalized good-parent exchange graph/source surgery','Complete algorithm/history/runtime and nonauthor review']}
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(rows))
