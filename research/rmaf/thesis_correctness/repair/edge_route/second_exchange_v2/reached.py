from transport import *
import importlib.util,random,argparse
p=argparse.ArgumentParser();p.add_argument('--limit',type=int,default=20);p.add_argument('--n',type=int,default=5);p.add_argument('--seed',type=int,default=622);args=p.parse_args()
controls();source=ROOT/'research/rmaf/thesis_correctness/algorithm.py';spec=importlib.util.spec_from_file_location('second_generator',source);alg=importlib.util.module_from_spec(spec);sys.modules[spec.name]=alg;spec.loader.exec_module(alg)
tt=old.trees(tuple('abcdefg'[:args.n]));rng=random.Random(args.seed)
pairs=list(it.product(tt,tt));rng.shuffle(pairs);pairs=pairs[:args.limit]
orig=alg.branches;counts={'inputs':0,'2B_calls':0,'unique_2B_states':0,'root_v_states':0,'K_premises':0,'lifted_second_premises':0,'root_v_K_premises':0};seen=set();first=None;firstroot=None;failures=[];current={};times=[]
def watch(f1,f2,av,cv,a,c):
 global first,firstroot
 result=orig(f1,f2,av,cv,a,c)
 if result[0]=='2B':
  counts['2B_calls']+=1;F=old.active_graph(f2);P,u=F.path(a,c);v=F.parent[u];x=next(w for w in F.children[v] if w!=u)
  key=repr((current['trees'],F.parent,F.labels,a,c,x))
  if key not in seen:
   seen.add(key);counts['unique_2B_states']+=1;S=structural(F,a,c,x);root=F.parent[v] is None;counts['root_v_states']+=root
   for C in old.powers(F.edges-(S['B']|S['P'])):
    try:r=check_transport(F,a,c,x,S['B']|C)
    except AssertionError as err:
     failures.append({'input':current,'F':F.json(),'a':a,'c':c,'x':x,'K':sorted(S['B']|C),'error':str(err)});raise
    counts['K_premises']+=1;counts['lifted_second_premises']+=1;counts['root_v_K_premises']+=root
    r['reached_input']=dict(current)
    if first is None:first=r
    if root and firstroot is None:firstroot=r
 return result
alg.branches=watch;start=time.perf_counter()
for i,(t1,t2) in enumerate(pairs):
 before=time.perf_counter();current={'index':i,'trees':[t1,t2]}
 for k in range(args.n):current['budget']=k;alg.decide(t1,t2,k)
 counts['inputs']+=1;times.append(time.perf_counter()-before)
 if (i+1)%100==0:print(json.dumps({'completed':i+1,'elapsed_seconds':time.perf_counter()-start,'K_premises':counts['K_premises']}),flush=True)
r={'status':'NO-FIRE','scope':'actual reached 2B states; graph transport only; every K with B subset K and K disjoint P enumerated per retained state','n':args.n,'limit':args.limit,'seed':args.seed,'counts':counts,'first_witness':first,'first_component_root_witness':firstroot,'failures':failures,'per_input_seconds':times,'elapsed_seconds':time.perf_counter()-start,'generator_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256((HERE/'transport.py').read_bytes()).hexdigest()}
old.atomic(RESULTS/f'thesis-correctness-repair-edge-second-reached-n{args.n}-limit{args.limit}.json',r)
print(json.dumps({'status':r['status'],'counts':counts,'elapsed_seconds':r['elapsed_seconds']}))
