"""One-shot structurally valid forest-pair census; independent of reached generator."""
from adversary import *
import argparse,random
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=3);p.add_argument('--limit',type=int,default=100);p.add_argument('--seed',type=int,default=615);a=p.parse_args()
controls();tt=trees(tuple('abcdef'[:a.n]));rng=random.Random(a.seed)
# Shuffled finite state identifiers retain both original source deletion masks.
width=2*a.n-1
universe=len(tt)**2*(1<<width)**2
indices=list(range(universe)) if universe<=100000 else None
if indices is not None:rng.shuffle(indices);indices=indices[:a.limit or len(indices)]
else:indices=rng.sample(range(universe),a.limit)
counts={'structural_candidates':0,'containment_valid_states':0,'noncontained_states':0,'checked_states':0,'pairs':0,'root_pairs':0,'cuts_enumerated':0,'af_cutsets':0,'normalization_premises':0,'root_premises_ge2':0,'root_premises_ge2_nonminimal':0};witnesses=[];first=None;times=[]
start=time.perf_counter()
for index in indices:
    before=time.perf_counter();z=index;m2=z%(1<<width);z//=1<<width;m1=z%(1<<width);z//=1<<width;j=z%len(tt);i=z//len(tt)
    T1,T2=Graph.tree(tt[i]),Graph.tree(tt[j]);D1=frozenset(e for k,e in enumerate(sorted(T1.edges)) if m1>>k&1);D2=frozenset(e for k,e in enumerate(sorted(T2.edges)) if m2>>k&1)
    F1,F2=T1.cut(D1).yielded_graph(),T2.cut(D2).yielded_graph();counts['structural_candidates']+=1
    if not containment(F1,F2):counts['noncontained_states']+=1
    else:
        counts['containment_valid_states']+=1
        if list(sibling_pairs(F1,F2)):
            meta={'kind':'structural-valid-not-asserted-reached','state_identifier':index,'T1_input':tt[i],'T2_input':tt[j],'initial_cut_ids_F1':sorted(D1),'initial_cut_ids_F2':sorted(D2)}
            cc,ww,ff=check_state(F1,F2,T1,T2,meta)
            counts['checked_states']+=1
            for k,v in cc.items():counts[k]+=v
            witnesses.extend(ww)
            if first is None and ff is not None:first=ff
    times.append(time.perf_counter()-before)
    if counts['structural_candidates']%100==0:print(json.dumps({'candidates':counts['structural_candidates'],'checked':counts['checked_states'],'elapsed_seconds':time.perf_counter()-start}),flush=True)
    if witnesses:break
result={'status':'FIRE' if witnesses else 'NO-FIRE','scope':'structurally valid states; no reachability claim; original initial deletion masks retained; all active original-edge cutsets in checked states','n':a.n,'limit':a.limit,'seed':a.seed,'state_universe_size':universe,'counts':counts,'elapsed_seconds':time.perf_counter()-start,'per_candidate_seconds':times,'counterexamples':witnesses,'first_structural_root_witness':first,'checker_sha256':hashlib.sha256((HERE/'adversary.py').read_bytes()).hexdigest()}
atomic(RESULTS/f'thesis-correctness-repair-edge-structural-n{a.n}-limit{a.limit}.json',result)
print(json.dumps({'status':result['status'],'counts':counts,'elapsed_seconds':result['elapsed_seconds']}),flush=True)
