"""Post hoc geometric-lemma diagnostics; neither held-out discovery nor proof."""
import json,time
from replay import Graph,inspect,advance,OUT
start=time.perf_counter()
f=Graph((('a',('x','y')),('p',('q','r'))))
g=Graph(('a',((('x','p'),'q'),('y','r'))))
f.protected.add(f.locate('a'));g.protected.update([g.locate('a'),g.locate('p,q,r,x,y')])
row=inspect(f,g,['x','y']);assert row['case']=='A3BC' and len(row['pendants'])==3 and all(x['legal'] for x in row['branches'])
ff,gg,k=advance(f,g,row,'C',5,4)
child=inspect(ff,gg,['x','a']);assert len(child['pendants'])==3
assert [b['name'] for b in child['branches'] if b['legal']]==['B']
# Delete the deeper-first hypothesis: x is shallow, y deep, all three J cuts
# are otherwise legal, but cutting y leaves a single-pendant a--x path.
bad=Graph(('a',('x',((('y','p'),'q'),'r'))))
bad.protected.update([bad.locate('a'),bad.locate('p,q,r,x,y')])
assert len(bad.pendants(bad.locate('x'),bad.locate('y')))==3
orientation_caught=False
try:inspect(f,bad,['x','y'])
except AssertionError as e:orientation_caught=str(e)=='wrong deeper-first orientation'
assert orientation_caught
bad.protected.add(bad.locate('x'));yy=bad.locate('y');bad.cut(yy);bad.remove_component(yy)
badps=bad.pendants(bad.locate('a'),bad.locate('x'))
assert len(badps)==1 and bad.legal(badps)
result={'scope':'post hoc diagnostics for the proposed two-leaf repair lemma, not a universal proof',
        'live_three_pendant_C_child':child,'corrupted_orientation_detected':orientation_caught,
        'missing_orientation_counterexample_pendant_count':len(badps),'elapsed_seconds':time.perf_counter()-start}
(OUT/'thesis-complexity-review-repair-controls.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'live_C_child_pendants':3,'wrong_orientation_rejected':True,'without_orientation_pendants':1,'elapsed_seconds':result['elapsed_seconds']}))
