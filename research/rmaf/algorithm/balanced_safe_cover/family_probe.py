#!/usr/bin/env python3
"""One-shot restricted product-family probe; development oracle only.
Generator is explicit and does not call the oracle. Exact scoring reuses the
documented pure-bridge graph instrument, so it is not independent verification.
"""
import argparse, hashlib, importlib.util, json, math, pathlib, time

ROOT=pathlib.Path(__file__).resolve().parents[4]
HERE=pathlib.Path(__file__).resolve().parent
ORACLE_PATH=ROOT/'research/rmaf/pure_bridge/check_geometry.py'
spec=importlib.util.spec_from_file_location('geometry_development',ORACLE_PATH)
geometry=importlib.util.module_from_spec(spec)
spec.loader.exec_module(geometry)

def family(r):
    source=target=0
    for i in range(r):
        a,b,c=3*i+1,3*i+2,3*i+3
        source=(((a,c),b),source)
        target=(((a,b),c),target)
    return source,target

def generate(r,budget):
    # Family recognition is by its supplied r-indexed constructor in this probe.
    # A universal arbitrary-input recognizer and graph proof are not supplied.
    if budget<r:return []
    singletons=tuple((3*i+1,) for i in range((r+1)//2))
    removed={x for b in singletons for x in b}
    remainder=tuple(x for x in range(3*r+1) if x not in removed)
    return [tuple(sorted(singletons+(remainder,)))]

def original_cuts_and_partition(source,blocks):
    singleton_labels=[b[0] for b in blocks if len(b)==1 and b[0]!=0]
    cuts=[]
    for label in singleton_labels:
        v=source.labels[label]
        if len(source.adj[v])!=1:raise AssertionError('not pendant')
        cuts.append(tuple(sorted((v,next(iter(source.adj[v]))))))
    removed=set(cuts); unseen=set(source.adj); regions=[]
    while unseen:
        seed=min(unseen); todo=[seed]; unseen.remove(seed)
        for v in todo:
            for w in source.adj[v]&unseen:
                if tuple(sorted((v,w))) not in removed:
                    unseen.remove(w);todo.append(w)
        labels=tuple(sorted(x for x,v in source.labels.items() if v in todo))
        if not labels:raise AssertionError('empty source region')
        regions.append(labels)
    assert tuple(sorted(regions))==blocks
    assert len(set(cuts))==len(cuts)==len(blocks)-1
    return cuts

def refines(partition,cover):
    return all(any(set(b)<=set(c) for c in cover) for b in partition)

def row(case):
    started=time.monotonic(); r=case['r']; syntaxS,syntaxT=family(r)
    S=geometry.Tree(syntaxS);T=geometry.Tree(syntaxT)
    generated=generate(r,case['budget']);assert len(generated)==1
    cover=generated[0]; cuts=original_cuts_and_partition(S,cover)
    oracle_started=time.monotonic(); originals=geometry.local_candidates(T,S)
    original_cost=originals[0]['cost']; optima=[p for p in originals if p['cost']==original_cost]
    source_parts=[geometry.Tree(S.shape(c)) for c in cover]
    locals_=[geometry.local_candidates(T,d) for d in source_parts]
    distances=[p[0]['cost'] for p in locals_];tau=max(distances,default=0)
    completion,witness=geometry.brute_completion(T,source_parts)
    survivors=[p['blocks'] for p in optima if refines(p['blocks'],cover)]
    spans=[T.span(c) for c in cover]
    pure=all(all(T.degree(v,spans[i])==T.degree(v,spans[j])==2 for v in spans[i]&spans[j])
             for i in range(len(spans)) for j in range(i))
    actual={'original_optimum':original_cost,'original_optima':len(optima),'precuts':len(cuts),
            'tau':tau,'completion':completion,'surviving_original_optima':len(survivors),
            'outputs':len(generated)}
    for k,v in actual.items():assert v==case['expected_'+k],{'field':k,'actual':v,'expected':case['expected_'+k]}
    assert pure and 2*tau<=case['budget'] and survivors
    assert len(cuts)+completion==original_cost
    assert generate(r,r-1)==[]
    wrong_accounting_caught=(r==0 or len(cuts)+completion!=completion)
    if not wrong_accounting_caught:raise AssertionError('charge corruption survived')
    return {'r':r,'n':case['n'],'budget':case['budget'],'source':syntaxS,'target':syntaxT,
            'cover':cover,'cuts':cuts,'actual':actual,'local_distances':distances,
            'pure':pure,'survivors':survivors,'witness':[w['blocks'] for w in witness],
            'oracle_seconds':time.monotonic()-oracle_started,'seconds':time.monotonic()-started,
            'scope':'production development; exact scoring oracle is absent from generate'}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-r',type=int,default=1)
    ap.add_argument('--output',default='algorithm-balanced-cover-family-pilot.json');args=ap.parse_args()
    fixture_path=HERE/'PRODUCT-FAMILY-CONTROLS.json';fixtures=json.loads(fixture_path.read_text())
    control_started=time.monotonic(); baseline=geometry.controls();control_seconds=time.monotonic()-control_started
    # Known trivial value before any product-family scoring.
    singleton=geometry.Tree(0);assert geometry.local_candidates(singleton,singleton)[0]['cost']==0
    cases=[c for c in fixtures['cases'] if c['r']<=args.max_r]
    if len(cases)!=args.max_r+1:raise AssertionError('unexpected probe denominator')
    rows=[row(c) for c in cases]
    report={'kind':'restricted-product-family-development-probe','status':'passed',
      'expected_cases':len(cases),'executed_cases':len(rows),'rows':rows,
      'baseline_controls':baseline,'baseline_control_seconds':control_seconds,
      'fixture_sha256':hashlib.sha256(fixture_path.read_bytes()).hexdigest(),
      'oracle_sha256':hashlib.sha256(ORACLE_PATH.read_bytes()).hexdigest(),
      'script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
      'total_seconds':control_seconds+sum(c['seconds'] for c in rows),
      'scope':'Restricted product family only; no universal safe-cover generator or complexity improvement.'}
    output=ROOT/'research/rmaf/results'/args.output;output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'passed','cases':len(rows),'row_seconds':[c['seconds'] for c in rows],
                      'receipt':str(output)}))

if __name__=='__main__':main()
