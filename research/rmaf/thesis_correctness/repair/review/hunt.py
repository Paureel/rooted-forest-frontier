"""One-shot exact finite adversary, importing only this review's fresh evaluator."""
from fresh_exact import *
from functools import lru_cache
import argparse

@lru_cache(None)
def shapes(labels):
    if len(labels)==1:return (labels[0],)
    out=[]; first=labels[0];rest=labels[1:]
    for k in range(len(rest)):
        for extra in combinations(rest,k):
            left=(first,)+extra;right=tuple(x for x in rest if x not in extra)
            for a in shapes(left):
                for b in shapes(right):out.append((a,b))
    return tuple(out)

def fragment(t,v,cuts):
    out=set()
    for label in t.cluster[v]:
        w=t.at[label]
        while w!=v and w not in cuts:w=t.parent[w]
        if w==v:out.add(label)
    return out

def component_labels(t,v,cuts):
    def top(w):
        while w in t.parent and w not in cuts:w=t.parent[w]
        return w
    topv=top(v)
    return {l for w,l in t.labels.items() if top(w)==topv}

def normal(t,cuts,path,u,initial):
    d=cuts & path;out=cuts-d
    if len(d)>=2 and u in t.parent and u not in initial:out.add(u)
    return out

def run(limit=0,n=4):
    start=time.perf_counter(); counts=dict(tree_pairs=0,AF_cutsets=0,N_premises=0,N_anchor_premises=0,compound_N=0,root_boundary_N=0,empty_repairs=0,min_survival_checks=0)
    bugs=[];examples={}; family=shapes(tuple('abcde'[:n]))
    for shape1 in family:
      a=Tree(shape1)
      for shape2 in family:
        b=Tree(shape2);counts['tree_pairs']+=1
        common={v:b.edge_for[c] for v,c in a.cluster.items() if c in b.edge_for and a.restriction(c)==b.restriction(c)}
        pairs=[(common[x],common[y]) for kids in a.children.values() if len(kids)==2 for x,y in [kids] if x in common and y in common]
        for detached1,detached2 in [(False,False),(False,True),(True,True)]:
          ia={1} if detached1 else set();ib={1} if detached2 else set()
          if not all(any(bl<=old for old in a.components(ia)) for bl in b.components(ib)):continue
          available=sorted(set(b.parent)-ib); good=[]
          for mask in range(1<<len(available)):
            e={v for i,v in enumerate(available) if mask>>i&1}
            if af(a,b,ib|e):good.append(e)
          mincount=min(map(len,good))
          for e in good:
            counts['AF_cutsets']+=1
            for av,bv in common.items():
                if bv in ib:continue
                labels=b.cluster[bv];sv=fragment(b,bv,ib|e)
                if len(e)==mincount:
                    counts['min_survival_checks']+=1
                    if not sv:bugs.append({'kind':'minimum_empty','T1':shape1,'T2':shape2,'E':list(e),'v':bv})
                if sv:continue
                inside={v for v,c in b.cluster.items() if c<labels};iset=e&inside;new=(e-iset)|{bv}
                counts['empty_repairs']+=1
                ok=af(a,b,ib|new) and len(iset)>=2 and len(new)<len(e)
                if not ok:bugs.append({'kind':'empty-repair','T1':shape1,'T2':shape2,'E':list(e),'v':bv})
            for x,y in pairs:
                path=b.path_edges(x,y);u=b.lca([x,y])
                if path&ib:continue
                # An E2 subset deleting only off-corridor, off-endpoint edges exists.
                inside={v for v,c in b.cluster.items() if c<b.cluster[x] or c<b.cluster[y]}
                e2=e-path-inside
                if any(child not in e2 and fragment(b,child,ib|e2) for child in b.pendant_edges(x,y)):continue
                sx=fragment(b,x,ib|e);sy=fragment(b,y,ib|e);d=e&path;uc=component_labels(b,u,ib|e)
                outside=uc-(set(b.cluster[x])|set(b.cluster[y]))
                separated=(sx if not b.path_edges(x,u).isdisjoint(e) else sy)
                anchor=not(len(d)==1 and outside and separated) or bool(uc&(set(b.cluster[x])|set(b.cluster[y])))
                both=bool(sx and sy)
                if not anchor:continue
                counts['N_anchor_premises']+=1
                if both:counts['N_premises']+=1
                if both and (len(b.cluster[x])>1 or len(b.cluster[y])>1):counts['compound_N']+=1
                if both and u in ib and len(d)>=2:counts['root_boundary_N']+=1
                normalized=normal(b,e,path,u,ib)
                if not af(a,b,ib|normalized) or len(normalized)>len(e):
                    bugs.append({'kind':'N-anchor','T1':shape1,'T2':shape2,'initial1':list(ia),'initial2':list(ib),'E':list(e),'pair':[x,y],'new':list(normalized),'both':both})
            if bugs or (limit and counts['AF_cutsets']>=limit):
                return {'counts':counts,'bugs':bugs,'elapsed_seconds':time.perf_counter()-start,'exhaustive':False,'n':n}
    return {'counts':counts,'bugs':bugs,'elapsed_seconds':time.perf_counter()-start,'exhaustive':True,'n':n}

def partial_replay():
    f=json.loads((REPAIR/'edge_route/partial-boundary-frozen.json').read_text());a,b=Tree(f['T1']),Tree(f['T2']);e=b.edges(f['E_clusters']);part=e-b.edges(f['restore_only']);x,y=f['pair'];u=b.lca([b.at[x],b.at[y]]);full=normal(b,e,b.path_edges(x,y),u,set())
    actual={'original_AF':af(a,b,e),'partial_AF':af(a,b,part),'full_AF':af(a,b,full),'active_containment':True,'endpoints_intact':True,'optimum_cuts':optimum(a,b)[0],
            'E_count':len(e),'partial_cuts':[sorted(b.cluster[v]) for v in part],'full_cuts':[sorted(b.cluster[v]) for v in full]}
    for k,v in f.items():
        if k.startswith('expected_'):check_equal(actual[k.removeprefix('expected_')],v,k)
    return actual

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--limit',type=int,default=0);p.add_argument('--n',type=int,default=4);args=p.parse_args()
    r=run(args.limit,args.n);r['partial_replay']=partial_replay();r['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    name='pilot' if args.limit else 'n'+str(args.n)
    (ROOT/('results/thesis-correctness-repair-review-hunt-'+name+'.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));assert not r['bugs']
