#!/usr/bin/env python3
"""One-shot C6 family test; shared GLOBAL-C oracle, not independent review."""
import argparse
import hashlib
import json
from pathlib import Path
from datetime import datetime, timezone
from time import perf_counter
from exact_conflicts import trees, exact_row


def renamed(q, prefix):
    if isinstance(q,str):
        return prefix+q
    return tuple(renamed(x,prefix) for x in q)


def expand(q):
    if isinstance(q,str):
        return ('a'+q,'b'+q)
    return tuple(expand(x) for x in q)


def case(q,m):
    A = ['a'+str(i) for i in range(m)]
    B = ['b'+str(i) for i in range(m)]
    source,target = (renamed(q,'a'),renamed(q,'b')),expand(q)
    out = exact_row(source,target,[A,B],retain=True)
    expected = {'optimum':m,'precuts':1,'completion':m-1,'tau':0,'charged':m}
    for key,value in expected.items():
        assert out[key] == value,(q,key,value,out[key])
        assert out[key] != value+1
    assert out['surviving'] > 0
    return {'Q':q,'m':m,'source':source,'target':target,'actual':out,
            'expected':expected,'comparison_count':5,'mutation_catches':5,
            'positive_optimum_survival':True}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-m',type=int,default=3);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    assert 2 <= args.max_m <= 4
    start=perf_counter()
    # Sharp excluded case, then successful m=2 twin.
    negative=exact_row(('a0','b0'),('a0','b0'),[['a0'],['b0']],retain=True)
    assert negative['optimum']==0 and negative['surviving']==0 and negative['charged']==1
    rows=[]
    for m in range(2,args.max_m+1):
        before=perf_counter();qs=trees(tuple(str(i) for i in range(m)))
        for q in qs:
            rows.append(case(q,m))
        print(json.dumps({'m':m,'Q_count':len(qs),'seconds':perf_counter()-before}),flush=True)
    data={'kind':'GLOBAL-C-mixed-cherry-special-cover-tests','date':datetime.now(timezone.utc).isoformat(),
          'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'oracle_sha256':hashlib.sha256(Path(__file__).with_name('exact_conflicts.py').read_bytes()).hexdigest(),
          'protocol_sha256':hashlib.sha256(Path(__file__).with_name('SPEC-v3.md').read_bytes()).hexdigest(),
          'lineage':'shared GLOBAL-C oracle and author; fresh m4 points; not independent verification',
          'rows':rows,'negative_m1':negative,'seconds':perf_counter()-start,
          'comparisons':sum(r['comparison_count'] for r in rows),
          'mutation_catches':sum(r['mutation_catches'] for r in rows)+1,
          'verdict':'FINITE-SPECIAL-COVER-CHECKS-REPRODUCE'}
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'output':str(args.output),'Q_cases':len(rows),'comparisons':data['comparisons'],
                      'mutation_catches':data['mutation_catches'],'verdict':data['verdict']}),flush=True)


if __name__=='__main__':
    main()
