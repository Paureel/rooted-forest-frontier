"""Replay controls first, then exact finite comparisons; no universal claim.
Use: ./bootloops-python research/rmaf/thesis_correctness/replay.py --mode controls
or --mode pilot/sweep --leaves 4/5/6 --limit N --seed S.
"""
import argparse, hashlib, itertools, json, random, time
from pathlib import Path
from reference import optimum, validate_pair
from algorithm import decide

HERE=Path(__file__).resolve().parent
RESULTS=HERE.parent/'results'

def exact_compare(expected, actual):
    if type(expected) is not type(actual) or expected != actual:
        raise AssertionError(f'exact comparison failed: expected={expected!r}, actual={actual!r}')


def controls():
    spec=json.loads((HERE/'controls.json').read_text())
    rows=[]
    for x in spec['known_answers']:
        q,w=optimum(x['t1'],x['t2'])
        exact_compare(x['optimum_cuts'],q)
        for b in range(-1,q+2): exact_compare(b>=q,decide(x['t1'],x['t2'],b))
        rows.append({'id':x['id'],'pass':True,'optimum_cuts':q,'witness':w})
    for x in spec['corruptions']:
        if x['id']=='wrong-expected-optimum':
            target=next(y for y in spec['known_answers'] if y['id']==x['target'])
            actual=optimum(target['t1'],target['t2'])[0]
            try: exact_compare(x['mutated_optimum_cuts'],actual)
            except AssertionError as exc: rows.append({'id':x['id'],'caught':True,'reason':str(exc)})
            else: raise AssertionError('planted wrong optimum escaped comparator')
        elif x['id']=='negative-budget':
            target=next(y for y in spec['known_answers'] if y['id']==x['target'])
            exact_compare(False,decide(target['t1'],target['t2'],-1))
            rows.append({'id':x['id'],'caught':True})
        else:
            for fn in (validate_pair, lambda a,b:decide(a,b,0)):
                try: fn(x['t1'],x['t2'])
                except ValueError: pass
                else: raise AssertionError(f'{x["id"]} escaped {fn}')
            rows.append({'id':x['id'],'caught':True,'routes':2})
    return rows


def trees(xs):
    if len(xs)==1: return (xs[0],)
    first,*rest=xs
    out=[]
    # Each unordered root split occurs once: first is in its first part.
    for bits in range(1<<len(rest)):
        left=[first]+[x for i,x in enumerate(rest) if bits>>i&1]
        right=[x for i,x in enumerate(rest) if not(bits>>i&1)]
        if not right: continue
        for a in trees(left):
            for b in trees(right): out.append((a,b))
    return tuple(out)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--mode',choices=['controls','pilot','sweep'],default='controls')
    ap.add_argument('--leaves',type=int,default=4)
    ap.add_argument('--limit',type=int,default=0)
    ap.add_argument('--seed',type=int,default=612)
    ar=ap.parse_args()
    start=time.perf_counter()
    report={'scope':'finite testing, not a universal correctness proof','mode':ar.mode,'controls':controls(),
            'hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [HERE/'controls.json',HERE/'algorithm.py',HERE/'reference.py']},
            'n':ar.leaves,'seed':ar.seed,'completed':0,'failures':[],'stats':{},'timing_batches':[],'branch_witnesses':{}}
    if ar.mode!='controls':
        ts=trees(tuple(chr(97+i) for i in range(ar.leaves)))
        total=len(ts)**2
        ids=list(range(total)) if not ar.limit or ar.limit>=total else random.Random(ar.seed).sample(range(total),ar.limit)
        report['expected_pairs']=len(ids)
        report['tree_count']=len(ts)
        last=time.perf_counter()
        for i,k in enumerate(ids):
            t1,t2=ts[k//len(ts)],ts[k%len(ts)]
            q,w=optimum(t1,t2)
            stats={}; trace=[]
            try:
                for budget in range(-1,q+2):
                    got=decide(t1,t2,budget,stats,trace)
                    exact_compare(budget>=q,got)
            except Exception as exc:
                report['failures'].append({'index':k,'t1':t1,'t2':t2,'oracle_cuts':q,'oracle_witness':w,
                                           'error':repr(exc),'budget':budget,'trace':trace})
                break
            for key,v in stats.items(): report['stats'][key]=report['stats'].get(key,0)+v
            for event in trace:
                if event['case'] not in report['branch_witnesses']:
                    report['branch_witnesses'][event['case']]={'index':k,'t1':t1,'t2':t2,'oracle_cuts':q,'oracle_witness':w,'event':event,'full_trace':trace}
            report['completed']+=1
            if (i+1)%10==0:
                now=time.perf_counter(); report['timing_batches'].append({'completed':i+1,'seconds':now-last}); last=now
        report['denominator_complete']=report['completed']==report['expected_pairs']
    report['seconds']=time.perf_counter()-start
    report['pass']=not report['failures'] and (ar.mode=='controls' or report['denominator_complete'])
    dest=RESULTS/f'thesis-correctness-{ar.mode}-n{ar.leaves}-limit{ar.limit}-seed{ar.seed}.json'
    dest.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'file':str(dest),'pass':report['pass'],'completed':report['completed'],'seconds':report['seconds'],
                      'stats':report['stats'],'failures':report['failures'][:1]},indent=2))
    if not report['pass']: raise SystemExit(1)

if __name__=='__main__': main()
