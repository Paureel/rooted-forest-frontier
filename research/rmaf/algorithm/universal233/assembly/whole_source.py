"""One-shot whole-source candidate integration; imports are DEVELOPMENT.
Wraps existing exact source core/graph/tidy/query instruments; no new solver.
"""
from pathlib import Path
import sys,json,time,hashlib
D=Path(__file__).resolve().parent;sys.path.insert(0,str(D.parent))
from scaffold_vertex_replay import *

if __name__=='__main__':
 start=time.perf_counter();ctls=controls();probe=generate([0,[1,2]],{0:0,1:1,2:2});assert [e['cost'] for e in probe['cores']]==[2]
 b=json.loads((ROOT/'results/algorithm-universal233-pair-charging-fire-v1.json').read_text())['witness'];s=Tree(b['original_Tprime']);red=b['reduced'];fs=red['forest_trees'];ex={int(k):v for k,v in red['expansion'].items()};parents=json.loads((ROOT/'results/algorithm-universal233-pair-fire-original-cuts-v3.json').read_text())['source_parents'];origparents=[set().union(*(set(ex[x]) for x in Tree(f).labels)) for f in fs];assert set().union(*origparents)==s.labels
 c=Fraction(233,100);rows=[]
 for vr in b['vertex_rows']:
  score=2/c;rr={'vertex':vr['vertex'],'branches':[]}
  for i in [0,1]:
   local=region_colors(Tree(red['T']),vr['vertex'],Tree(fs[i]).labels);col={};colorid=0
   for j,p in enumerate(origparents):
    if j==i:
     for x,z in local.items():
      for original in ex[x]:col[original]=colorid+z
     colorid+=len(set(local.values()))
    else:
     for x in p:col[x]=colorid
     colorid+=1
   assert set(col)==s.labels and len(set(col.values()))==colorid
   g=generate(s.raw,col);rawmass=sum(c**(-o['cost']) for o in g['cores']);dyadic=sum(Fraction(1,2)**o['cost'] for o in g['cores']);assert dyadic<=Fraction(2)**(1-colorid)
   es=[];mass=Fraction(0)
   for o in g['cores']:
    assert o['cost']>=colorid-1
    assert all(sum(set(part)<=p for p in origparents)==1 for part in o['partition'])
    r=tidy(b['original_T'],[s.restriction(part) for part in o['partition']]);m,cont=paid_next(r['T'],r['forest_trees'],c);mass+=c**(-o['cost'])*m;es.append({'cost':o['cost'],'partition':o['partition'],'cuts':o['cuts'],'continuation':cont})
   score+=mass;rr['branches'].append({'source_parent':i,'colors':col,'r_total':colorid,'costs':[o['cost'] for o in g['cores']],'raw_mass':str(rawmass),'dyadic_mass':str(dyadic),'after_paid_continuation_mass':str(mass),'emissions':es})
  rr['full_mass']=str(score);rows.append(rr)
 out={'controls':ctls,'three_color_paid2_control':True,'rows':rows,'minimum_full_mass':str(min(Fraction(r['full_mass']) for r in rows)),'elapsed_seconds':time.perf_counter()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((D/'WHOLE-SOURCE-PIN-v1.json').read_bytes()).hexdigest(),'scope':'Actual finite whole-source candidate calls/costs; source refinement and global state interfaces remain unproved; no improved algorithm claim.'};(ROOT/'results/algorithm-universal233-whole-source-pilot-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(out['minimum_full_mass'],out['elapsed_seconds'])
 for r in rows:print(r['vertex'],r['full_mass'],[(b['r_total'],b['costs'],b['after_paid_continuation_mass']) for b in r['branches']])
