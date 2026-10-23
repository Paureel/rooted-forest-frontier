"""One-shot scaffold profile classifier; not an rMAF solver or independent check.
Existing controlled multicolor prototype/oracle are DEVELOPMENT dependencies.
"""
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import importlib.util,json,sys,time,hashlib,argparse
ROOT=Path(__file__).resolve().parents[4]
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path)
    m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m
core=module('profiles_development_core',Path('research/rmaf/algorithm/x0/multicolor/prototype.py'))
oracle=module('profiles_development_oracle',Path('research/rmaf/algorithm/x0/fresh_oracle.py'))
c=Fraction(233,100)
def mass(p): return sum((c**(-d) for d in p),Fraction())
@lru_cache(None)
def profiles(n):
    if n==1:return frozenset({(1,)})
    return frozenset(tuple(sorted(d+1 for d in a+b)) for j in range(1,n) for a in profiles(j) for b in profiles(n-j))
def canonical(p): return sorted(sorted(b) for b in p)
def run_source(t,col,**kw):
    r=core.generate(t,col,**kw);g=oracle.Tree(t)
    for e in r['raw_cores']:
        blocks,empty=g.cut_blocks(e['cuts'])
        assert not empty,empty
        assert canonical(blocks)==canonical(e['partition'])
        assert len(blocks)==len(e['cuts'])+1
    return {'tree':t,'colors':col,'raw_profile':sorted(e['cost'] for e in r['raw_cores']),
            'raw_emissions':len(r['raw_cores']),'deduplicated_emissions':len(r['cores']),
            'cut_witnesses':r['raw_cores'],'stats':r['stats']}
def controls():
    src=[]
    for t,col,want in [(((0,1),2),{0:0,1:0,2:1},[1]),
      (((0,1),(2,3)),{0:0,1:1,2:0,3:1},[2,2]),
      (((0,1),(2,(3,4))),{0:0,1:1,2:0,3:0,4:1},[2,3,3]),
      (7,{7:0},[0])]:
        r=run_source(t,col);assert r['raw_profile']==want,(r['raw_profile'],want);src.append(r)
    q=((0,1),(2,3));cols={0:0,1:1,2:0,3:1}
    omitted=run_source(q,cols,omit_first_mixed_right=True)
    assert omitted['raw_profile']!=[2,2]
    pruned=run_source(q,cols,budget=1);assert pruned['raw_profile']==[]
    assert mass([])==0
    assert mass([2,3,4,4])>mass([3,3,3,3])
    assert mass([1,1,3,4,5,6,6])==Fraction(159752208278600,160005726539569)<1
    assert mass([1,1,3,4,4])>1
    pairs=[]
    small=[(1,),(2,2),(2,3,3)]
    for i,a in enumerate(small):
      for b in small[i:]:
        m=2/c+(mass(a)+mass(b))/c**2
        expected=(a==(1,))
        assert (m>1)==expected,(a,b,m)
        pairs.append({'left':a,'right':b,'full_mass':str(m),'unsafe':m>1})
    ladders=[]
    for n in (1,2,3,4,8,16):
        t=(0,1)
        for label in range(2,n+1):t=(label,t)
        col={i:int(i!=0) for i in range(n+1)}
        r=run_source(t,col)
        norm,_=core.normalize(core.read_source(t,col),col)
        assert len(core.groups(norm))==n+1
        assert r['raw_profile']==[1]
        ladders.append({'B_count':n,'normalized_group_count':n+1,'raw_profile':r['raw_profile'],'source_cut':r['cut_witnesses'][0]['cuts']})
    assert ladders[3]['normalized_group_count']>3
    return {'source_controls':src,'missing_branch_caught':omitted,'budget_pruned':pruned,
            'arithmetic_negative_caught':True,'balanced_false_bound_caught':True,'small_pairs':pairs,
            'unbounded_attachment_ladder_controls':ladders,'false_group_bound_caught':True}
def main():
    p=argparse.ArgumentParser();p.add_argument('--max-leaves',type=int,default=6);p.add_argument('--output',required=True);p.add_argument('--pilot');a=p.parse_args()
    out=ROOT/a.output
    if out.exists():raise FileExistsError(out)
    if a.max_leaves>6:
        pilot=json.loads((ROOT/a.pilot).read_text());assert pilot['max_leaves']==6 and pilot['verdict']=='FINITE-NO-FIRE'
    start=time.monotonic();ct=controls();rows=[]
    for n in range(1,a.max_leaves+1):
        t=time.monotonic();ps=profiles(n);best=max(ps,key=mass)
        assert all(sum(Fraction(1,2)**d for d in x)==Fraction(1,2) for x in ps)
        if n>=4:assert all(mass(x)<=mass((2,3,4,4)) for x in ps)
        rows.append({'leaves':n,'distinct_profiles':len(ps),'maximum_profile':best,'maximum_mass':str(mass(best)),'seconds':time.monotonic()-t})
    files=[Path(__file__),ROOT/'research/rmaf/algorithm/x0/multicolor/prototype.py',ROOT/'research/rmaf/algorithm/x0/fresh_oracle.py',ROOT/'research/rmaf/algorithm/scaffold_profiles/CONTROLS-PIN-v1.md']
    result={'scope':'Development finite exact source/profile controls; no universal source/target or runtime certification','verdict':'FINITE-NO-FIRE','max_leaves':a.max_leaves,'controls':ct,'rows':rows,'seconds':time.monotonic()-start,
            'source_sha256':{str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files}}
    out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'verdict':result['verdict'],'rows':rows,'seconds':result['seconds'],'output':str(out)}))
if __name__=='__main__':main()
