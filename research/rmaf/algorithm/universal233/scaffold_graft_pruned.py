"""One-shot exact necessary-condition pruning of the targeted graft family.
The complete earlier-rule predicate is still called before any state admission.
This restructures the v1 search rather than increasing its blind census.
"""
from scaffold_graft_search import *


def necessary(h,ar,br,na):
    ht=Tree(h);ats=[Tree(ar),Tree(br)];sets=[f.labels for f in ats]
    for p,q in ht.cherries():
        idx=next((i for i,s in enumerate(sets) if p in s and q in s),None)
        if idx is None:return False
        if len(ats[idx].pendant(p,q))!=2:return False
    for a in ats:
        for p,q in a.cherries():
            if len(ht.pendant(p,q))!=2:return False
    spans=[ht.span(s) for s in sets]
    return bool(spans[0]&spans[1])


def run_pruned(na,nb):
    start=time.perf_counter();c,x,y=range(na+nb,na+nb+3)
    count={'source_parent_pairs':0,'base_H_pairs':0,'necessary_survivors':0,'complete_candidate_pairs':0,'selected_cherry_controls':0,'earlier_excluded_both_orientations':0,'actual_hard_cherries':0,'pair_isolated_good_states':0,'expensive_boundaries':0}
    rows=[]
    for ar in trees(tuple(range(na))):
      for br in trees(tuple(range(na,na+nb))):
        count['source_parent_pairs']+=1
        for h in trees(tuple(range(na+nb))):
          count['base_H_pairs']+=1
          if not necessary(h,ar,br,na):continue
          count['necessary_survivors']+=1
          for s in source_six(ar,br,c,x,y):
            st=Tree(s)
            for raw in [[[c,h],[x,y]],[c,[[x,y],h]]]:
              tt=Tree(raw);assert [x,y] in tt.cherries();count['selected_cherry_controls']+=1
              count['complete_candidate_pairs']+=1
              adm=applicability(tt,st)
              if not adm['excluded_2a_to_2d']:continue
              reverse=applicability(st,tt)
              if not reverse['excluded_2a_to_2d']:continue
              count['earlier_excluded_both_orientations']+=1
              count['actual_hard_cherries']+=1;out=scan_child(raw,s,[x,y])
              if out is not None:
                count['pair_isolated_good_states']+=1;count['expensive_boundaries']+=len(out['expensive_boundaries']);rows.append(out)
    return {'a':na,'b':nb,'n':na+nb+3,'counts':count,'states':rows,'elapsed_seconds':time.perf_counter()-start,'scope':'Finite selected-cherry-verified graft family. Necessary pruning restricts measured search; no universal exclusion/coverage claim.'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--a',type=int,required=True);p.add_argument('--b',type=int,required=True);p.add_argument('--out',required=True);a=p.parse_args()
    out={'controls':controls(),'search':run_pruned(a.a,a.b),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((HERE/'SCAFFOLD-GRAFT-PIN-v2.json').read_bytes()).hexdigest()}
    Path(a.out).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out['search'].items() if k!='states'}))
