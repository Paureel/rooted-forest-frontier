"""One-shot targeted source-hard-child graft construction; DEVELOPMENT only.
Capability consultation/provenance: see scaffold_search.py and graft pin.
"""
from scaffold_search import *


def addresses(t,p=()):
    yield p
    if not isinstance(t,int):
        yield from addresses(t[0],p+(0,));yield from addresses(t[1],p+(1,))


def graft(t,p,u):
    if not p:return [t,u]
    s=list(t);s[p[0]]=graft(s[p[0]],p[1:],u);return s


def source_six(a,b,c,x,y):
    return [[c,[[x,a],[y,b]]], [c,[[x,b],[y,a]]],
            [c,[[[x,a],b],y]],[c,[[[x,b],a],y]],
            [c,[x,[[y,a],b]]],[c,[x,[[y,b],a]]]]


def run_grafts(na,nb):
    start=time.perf_counter();c,x,y=range(na+nb,na+nb+3);C=[c,[x,y]]
    count={'source_parent_pairs':0,'constructed_source_trees':0,'target_trees':0,'candidate_pairs':0,'earlier_excluded_both_orientations':0,'actual_hard_cherries':0,'pair_isolated_good_states':0,'expensive_boundaries':0}
    rows=[];control_count=0
    targets={repr(Tree(t).restriction(range(na+nb+3))):t for h in trees(tuple(range(na+nb))) for t in
             [*(graft(h,p,C) for p in addresses(h)),*(graft(C,p,h) for p in addresses(C))]}
    count['target_trees']=len(targets)
    for ar in trees(tuple(range(na))):
      for br in trees(tuple(range(na,na+nb))):
        count['source_parent_pairs']+=1
        for s in source_six(ar,br,c,x,y):
          count['constructed_source_trees']+=1;st=Tree(s);ps=st.pendant(x,y)
          assert len(ps)==2 and {tuple(z['labels']) for z in ps}=={tuple(range(na)),tuple(range(na,na+nb))}
          blocks,empty=st.cut_blocks([z['edge'] for z in ps]);assert not empty
          assert {tuple(z) for z in blocks}=={tuple(range(na)),tuple(range(na,na+nb)),(c,x,y)};control_count+=1
          for raw in targets.values():
            count['candidate_pairs']+=1;tt=Tree(raw)
            adm=applicability(tt,st)
            if not adm['excluded_2a_to_2d']:continue
            reverse=applicability(st,tt)
            if not reverse['excluded_2a_to_2d']:continue
            count['earlier_excluded_both_orientations']+=1
            count['actual_hard_cherries']+=1
            out=scan_child(raw,s,[x,y])
            if out is not None:
              count['pair_isolated_good_states']+=1;count['expensive_boundaries']+=len(out['expensive_boundaries']);rows.append(out)
    return {'a':na,'b':nb,'n':na+nb+3,'counts':count,'graft_controls_passed':control_count,'states':rows,'elapsed_seconds':time.perf_counter()-start,'scope':'Finite structurally generated family only; no universal assertion'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--a',type=int,required=True);p.add_argument('--b',type=int,required=True);p.add_argument('--out',required=True);a=p.parse_args()
    out={'controls':controls(),'search':run_grafts(a.a,a.b),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((HERE/'SCAFFOLD-GRAFT-PIN-v1.json').read_bytes()).hexdigest()}
    Path(a.out).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out['search'].items() if k!='states'}))
