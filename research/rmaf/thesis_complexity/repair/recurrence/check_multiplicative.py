#!/usr/bin/env python3
"""One-shot proposed measure adversary. Shares tree/table production code;
this is an explicit derivation check, never an independent certification."""
import json,time
from fractions import Fraction as F
import check_recurrence as cr
start=time.perf_counter()
def mw(p,q):
    assert 0<=q<=p<=3
    return F(3,2)**q/F(2)**p
freeze=json.loads((cr.HERE/'multiplicative-controls-frozen.json').read_text())
for row in freeze['hand_controls']:assert mw(row['p'],row['q'])==F(row['mass'])
cr.w=mw
rows=cr.tables();byid={r['id']:r for r in rows}
for row in freeze['row_controls']:
    r=byid[row['id']]
    for key in ('mass','target','offset'):
        if key in row:assert r[key]==row[key],(row,r)
    if 'must_fail' in row:assert r['pass_mass']!=row['must_fail']
fail=[r for r in rows if not (r['pass_mass'] and r['pass_offset'])]
assert {r['id'] for r in fail}=={'G4.1-A3-0-3','G4.1-A3-1-3'}
assert F(byid['lifted-G3-Q-nonempty-A2-1-1']['mass'])>F(1,2)
assert 0-6!=1-6
# A universal finite frontier composition can be normalized to C's budget:
# C <= alpha*2^(K-1)*M + v - 3*l. Source A and B bounds leave C
# allowance alpha*2^(K-3)+2. An exact alpha=128 boundary check permits
# M<=1/4 and v-3*l <=2+64*(1/4-M); the simpler alpha-free certificate
# M<=1/4, v-3*l<=2 is sufficient.
frontiers=[{'id':'dead-C','M':F(0),'v':1,'l':0},
           {'id':'two-cut-single-discharge','M':F(1,4),'v':1,'l':1},
           {'id':'three-cut-single-discharge','M':F(1,8),'v':1,'l':1},
           {'id':'one-cut-single-discharge-mutation','M':F(1,2),'v':1,'l':1},
           {'id':'one-cut-hard-credit-exit','M':F(1,4),'v':1,'l':1}]
# Last example uses one exit already bounded by a hard credit; its actual
# offset is -2 (not generic -3), so treat its offset explicitly.
for f in frontiers:
    f['offset']=f['v']-3*f['l']
    if f['id']=='one-cut-hard-credit-exit':f['offset']=-1
    f['simple_pass']=f['M']<=F(1,4) and f['offset']<=2
    f['fixed_alpha_pass']=f['M']<=F(1,4) and f['offset']<=2+64*(F(1,4)-f['M'])
    f['M']=str(f['M'])
assert [x['simple_pass'] for x in frontiers]==[True,True,True,False,True]
out={'status':'CONDITIONAL-ARITHMETIC-ONLY','measure':freeze['measure'],'metrics':{'states':10,'rows':len(rows),'passing_rows':len(rows)-len(fail),'exceptional_rows':len(fail),'elapsed_seconds':time.perf_counter()-start},'rows':rows,'failures':fail,'frontier_controls':frontiers,'independence':'Same author and table generator; fresh nonauthor check still required.'}
cr.atomic(cr.RESULT/'thesis-runtime-repair-recurrence-multiplicative.json',out)
print(json.dumps({'status':out['status'],'metrics':out['metrics'],'exceptions':[r['id'] for r in fail]},sort_keys=True))
