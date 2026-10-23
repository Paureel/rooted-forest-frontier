"""One-shot finite exact feature index for the same source scaffold hunt.
No production optimizer/oracle; all development contacts remain burned.
"""
from scaffold_graft_pruned import *
from collections import Counter


def run_features(na,nb):
    start=time.perf_counter();c,x,y=range(na+nb,na+nb+3);sets=[set(range(na)),set(range(na,na+nb))]
    pairs=[p for s in sets for p in combinations(sorted(s),2)];index={tuple(p):1<<i for i,p in enumerate(pairs)}
    def mask(cherries):return sum(index[tuple(p)] for p in cherries)
    def source_features(ar,br):
        aa,bb=Tree(ar),Tree(br);allowed=0
        for p,bit in index.items():
            f=aa if p[0]<na else bb
            if len(f.pendant(*p))==2:allowed|=bit
        return mask(aa.cherries()+bb.cherries()),allowed
    hfeatures=[];hcount=0
    for h in trees(tuple(range(na+nb))):
        hcount+=1;ht=Tree(h);ch=ht.cherries()
        if any((p<na)!=(q<na) for p,q in ch):continue
        if not ht.span(sets[0])&ht.span(sets[1]):continue
        t2=sum(bit for p,bit in index.items() if len(ht.pendant(*p))==2)
        hfeatures.append((h,mask(ch),t2))
    feature_seconds=time.perf_counter()-start
    count={'H_trees':hcount,'H_feature_candidates':len(hfeatures),'source_parent_pairs':0,'base_H_pairs':0,'necessary_survivors':0,'complete_candidate_pairs':0,'selected_cherry_controls':0,'earlier_excluded_both_orientations':0,'actual_hard_cherries':0,'pair_isolated_good_states':0,'expensive_boundaries':0}
    rows=[];reject=Counter()
    for ar in trees(tuple(range(na))):
      for br in trees(tuple(range(na,na+nb))):
        count['source_parent_pairs']+=1;sch,st2=source_features(ar,br)
        for h,hch,ht2 in hfeatures:
          count['base_H_pairs']+=1
          if hch&~st2 or sch&~ht2:continue
          count['necessary_survivors']+=1
          for s in source_six(ar,br,c,x,y):
            st=Tree(s)
            for raw in [[[c,h],[x,y]],[c,[[x,y],h]]]:
              tt=Tree(raw);assert [x,y] in tt.cherries();count['selected_cherry_controls']+=1
              count['complete_candidate_pairs']+=1
              adm=applicability(tt,st);reverse=applicability(st,tt)
              if not adm['excluded_2a_to_2d'] or not reverse['excluded_2a_to_2d']:
                for orient,obj in [('forward',adm),('reverse',reverse)]:
                  for name in ['step2a','step2b','step2c','step2d']:
                    if any(r[name] for r in obj['rows']):reject[orient+'_'+name]+=1
                continue
              count['earlier_excluded_both_orientations']+=1;count['actual_hard_cherries']+=1
              out=scan_child(raw,s,[x,y])
              if out is not None:
                count['pair_isolated_good_states']+=1;count['expensive_boundaries']+=len(out['expensive_boundaries']);rows.append(out)
    if (na,nb)==(4,2):
        assert count['necessary_survivors']==48 and count['complete_candidate_pairs']==576
    return {'a':na,'b':nb,'n':na+nb+3,'counts':count,'rejection_counts':dict(reject),'states':rows,'feature_seconds':feature_seconds,'elapsed_seconds':time.perf_counter()-start,'scope':'Finite exact-feature restricted development search; universal pruning proof/independent verification not claimed'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--a',type=int,required=True);p.add_argument('--b',type=int,required=True);p.add_argument('--out',required=True);a=p.parse_args()
    out={'controls':controls(),'search':run_features(a.a,a.b),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256((HERE/'SCAFFOLD-FEATURE-PIN-v1.json').read_bytes()).hexdigest()}
    Path(a.out).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out['search'].items() if k!='states'}))
