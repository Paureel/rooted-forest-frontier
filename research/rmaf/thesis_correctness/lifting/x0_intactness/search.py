#!/usr/bin/env python3
"""One-shot X0 bounded search driver; no imported external RMAF machinery.
All minima are actual current-F2 edge sets. No finite outcome is a proof.
"""
from __future__ import annotations
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import argparse
import hashlib
import json
import os
import random
import time
from evaluator import Forest, all_cutsets, run_controls

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[2]
PROGRESS=BASE/'progress/thesis-correctness-lifting-x0-intactness.json'


def json_ready(x):
    if isinstance(x, dict): return {str(k):json_ready(v) for k,v in x.items()}
    if isinstance(x,(tuple,list,set,frozenset)): return [json_ready(v) for v in x]
    return x


def atomic_write(path, data):
    path.parent.mkdir(parents=True,exist_ok=True)
    temporary=path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(json_ready(data),indent=2)+'\n'); os.replace(temporary,path)


def progress(status,summary,metrics,artifacts):
    atomic_write(PROGRESS,{'id':'thesis-correctness-lifting-x0-intactness','title':'X0 common pendant subtree intactness',
                         'status':status,'summary':summary,'metrics':metrics,
                         'claims':[{'id':'S_every','label':'Every minimum intact','status':'open','detail':'Fresh bounded X0 search; no universal inference.'},
                                   {'id':'S_exists','label':'An intact minimum exists','status':'open','detail':'Tracked separately from every-optimum violations.'},
                                   {'id':'S_contract','label':'Contraction interface','status':'open','detail':'Expansion, AF acceptance and cut-cost checks on tested pairs.'}],
                         'lemmas':[], 'artifacts':[str(p.resolve()) for p in artifacts]})


@lru_cache(None)
def rooted_trees(labels):
    labels=tuple(sorted(labels))
    if len(labels)==1: return (labels[0],)
    result=[]
    first=labels[0]
    rest=labels[1:]
    for k in range(len(rest)):
        for subset in combinations(rest,k):
            left=(first,)+subset; right=tuple(x for x in rest if x not in subset)
            for a in rooted_trees(left):
                for b in rooted_trees(right): result.append(tuple(sorted((a,b),key=repr)))
    return tuple(sorted(set(result),key=repr))


@lru_cache(None)
def by_signature(signature): return Forest.from_signature(signature)


@lru_cache(None)
def deletions(signature):
    f=by_signature(signature)
    rows=[]
    for cut in all_cutsets(f):
        out,empty=f.yielded(cut)
        rows.append((cut,out,len(empty)))
    return tuple(rows)


@lru_cache(None)
def outputs(signature): return frozenset(row[1] for row in deletions(signature))


@lru_cache(None)
def blocks(signature):
    def labels(t): return frozenset(([t[0]] if t[0] else []) + [x for c in t[1] for x in labels(c)])
    return tuple(labels(t) for t in signature)


def compatible(sig1,sig2): return all(any(b2<=b1 for b1 in blocks(sig1)) for b2 in blocks(sig2))


def minima(sig1,sig2,forced=frozenset()):
    accepted1=outputs(sig1); result=[]; best=None
    for cut,out,empty in deletions(sig2):
        if best is not None and len(cut)>best: break
        if forced<=cut and out in accepted1:
            best=len(cut); result.append((cut,out,empty))
    assert result
    return best,result


@lru_cache(None)
def common_candidates(signature): return by_signature(signature).proper_subtrees()


def witness(sig1,sig2,A,best,mins):
    f2=by_signature(sig2)
    return {'F1':by_signature(sig1).record(),'F2':f2.record(),'A':sorted(A),'optimum':best,
            'internal_edges':sorted(f2.internal_edges(A)),
            'all_minima':[{'edges':sorted(c),'clusters':f2.cut_clusters(c),'yield':out,'empty_components':empty} for c,out,empty in mins]}


def check_contraction(sig1,sig2,A,best,counts):
    f1,f2=by_signature(sig1),by_signature(sig2)
    q1,q2=f1.contracted(A),f2.contracted(A)
    qsig1,qsig2=q1.yielded()[0],q2.yielded()[0]
    contracted_opt,qmins=minima(qsig1,qsig2)
    counts['contracted_optimum_comparisons']+=1
    if contracted_opt != best:
        return {'type':'contraction_optimum_mismatch','original_optimum':best,'contracted_optimum':contracted_opt}
    # Canonical rebuild ensures quotient edge IDs agree with deletions(qsig2).
    q2=by_signature(qsig2)
    original_cluster_edges={cl:e for e,cl in f2.clusters().items()}
    qcluster=q2.clusters()
    def expand_labels(cl): return (cl-{'alpha'})|A if 'alpha' in cl else cl
    mapping={e:original_cluster_edges[expand_labels(cl)] for e,cl in qcluster.items()}
    A_signature=common_candidates(sig2)[A]
    def expand(t):
        if t[0]=='alpha':
            assert not t[1]
            return A_signature
        return (t[0],tuple(sorted((expand(c) for c in t[1]),key=repr)))
    acceptance_original,acceptance_contracted=outputs(sig1),outputs(qsig1)
    for qcuts,qout,empty in deletions(qsig2):
        cuts=frozenset(mapping[e] for e in qcuts)
        out,_=f2.yielded(cuts)
        expanded=tuple(sorted((expand(t) for t in qout),key=repr))
        counts['contraction_cutset_correspondences']+=1
        counts['contraction_empty_fragment_cutsets']+=int(empty>0)
        if len(cuts)!=len(qcuts) or out!=expanded:
            return {'type':'expansion_or_cost_mismatch','cuts':cuts,'qcuts':qcuts,'out':out,'expanded':expanded}
        orig_AF=out in acceptance_original; q_AF=qout in acceptance_contracted
        counts['contraction_AF_correspondences']+=int(orig_AF and q_AF)
        if orig_AF!=q_AF:
            return {'type':'contraction_AF_mismatch','cuts':cuts,'qcuts':qcuts,'original_AF':orig_AF,'contracted_AF':q_AF}
    return None


def audit_pair(sig1,sig2,counts,findings,deep=True):
    counts['structural_pairs_considered']+=1
    if not compatible(sig1,sig2):
        counts['incompatible_pairs_excluded']+=1; return
    counts['compatible_pairs']+=1
    s1,s2=common_candidates(sig1),common_candidates(sig2)
    common=[A for A in s1.keys()&s2.keys() if s1[A]==s2[A]]
    same_cluster_wrong_topology=[A for A in s1.keys()&s2.keys() if s1[A]!=s2[A]]
    counts['same_cluster_wrong_topology_excluded']+=len(same_cluster_wrong_topology)
    if not common: return
    counts['pairs_with_identical_proper_pendant_subtrees']+=1
    f1,f2=by_signature(sig1),by_signature(sig2)
    best,mins=minima(sig1,sig2)
    counts['minimum_cutsets_pair_denominator']+=len(mins)
    counts['positive_optimum_pairs']+=int(best>0)
    counts[f'optimum_{best}_pairs']+=1
    counts['unlabelled_component_root_pairs']+=int(any(t[0]=='' for t in sig1+sig2))
    counts['unary_rho_pairs']+=int(any(t[0]=='rho' and len(t[1])==1 for t in sig1+sig2))
    counts['isolated_rho_pairs']+=int(any(t[0]=='rho' and not t[1] for t in sig1+sig2))
    counts['multiple_component_pairs']+=int(len(sig1)>1 or len(sig2)>1)
    counts['both_forests_multiple_component_pairs']+=int(len(sig1)>1 and len(sig2)>1)
    counts['strict_F2_component_refinement_pairs']+=int(set(blocks(sig1))!=set(blocks(sig2)))
    accepted=[r for r in deletions(sig2) if r[1] in outputs(sig1)] if deep else []
    inclusion_minimal=[r for r in accepted if not any(s[0]<r[0] for s in accepted)]
    for A in common:
        counts['common_subtree_occurrences']+=1
        internal=f2.internal_edges(A)
        violated=[r for r in mins if r[0]&internal]
        counts['minimum_cutsets_subtree_denominator']+=len(mins)
        counts['every_optimum_violating_cutsets']+=len(violated)
        counts['every_optimum_violation_occurrences']+=int(bool(violated))
        counts['existence_failure_occurrences']+=int(len(violated)==len(mins))
        if violated:
            findings.append(dict(witness(sig1,sig2,A,best,mins),type='S_every_violation',S_exists_fails=len(violated)==len(mins)))
        if deep:
            counts['arbitrary_AF_cutsets_subtree_denominator']+=len(accepted)
            counts['arbitrary_AF_nonintact_cutsets']+=sum(bool(c&internal) for c,_,_ in accepted)
            counts['arbitrary_AF_empty_fragment_cutsets']+=sum(empty>0 for _,_,empty in accepted)
            counts['inclusion_minimal_cutsets_subtree_denominator']+=len(inclusion_minimal)
            counts['inclusion_minimal_nonminimum_cutsets']+=sum(len(c)>best for c,_,_ in inclusion_minimal)
            counts['inclusion_minimal_nonintact_cutsets']+=sum(bool(c&internal) for c,_,_ in inclusion_minimal)
            for forced_edge in internal:
                forced_best,forced_mins=minima(sig1,sig2,frozenset([forced_edge]))
                counts['forced_extension_instances']+=1
                counts['forced_extension_minimum_cutsets']+=len(forced_mins)
                counts['forced_extension_nonintact_minima']+=sum(bool(c&internal) for c,_,_ in forced_mins)
                counts['forced_extension_increased_optimum']+=int(forced_best>best)
        trouble=check_contraction(sig1,sig2,A,best,counts)
        if trouble: findings.append(dict(witness(sig1,sig2,A,best,mins),**trouble))


def generate_current(n,rho):
    originals=[Forest.from_tree(t,rho).yielded()[0] for t in rooted_trees(tuple('abcdefg'[:n]))]
    seen={}
    raw_cutsets=0;empty_raw=0
    for signature in originals:
        for cuts,out,empty in deletions(signature):
            raw_cutsets+=1;empty_raw+=int(empty>0)
            if out not in seen: seen[out]={'origin_signature':signature,'origin_cutset':sorted(cuts)}
    return sorted(seen,key=repr),seen,{'source_tree_count':len(originals),'raw_source_cutsets':raw_cutsets,
                                    'source_cutsets_discarding_empty_fragments':empty_raw,'distinct_current_forests':len(seen)}


def run(args):
    started=time.perf_counter()
    # Every run replays the frozen controls before entering its search domain.
    control_path=args.receipt.with_name(args.receipt.stem+'-controls.json')
    if not run_controls(control_path): raise SystemExit(2)
    domains=[];findings=[]
    metadata={'evaluator_sha256':hashlib.sha256((HERE/'evaluator.py').read_bytes()).hexdigest(),
              'search_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'mode':args.mode,'max_n':args.max_n,'limit':args.limit,'seed':args.seed,
              'classification':'bounded exact finite-tested; universal claims remain open',
              'algorithm_reachability':'not tested; current forests are compatible structural cut/yield pairs',
              'deep_domain_checks':not args.shallow}
    for rho in (False,True):
        for n in range(3,args.max_n+1):
            counts=Counter();start=time.perf_counter()
            if args.mode=='whole':
                signatures=[Forest.from_tree(t,rho).yielded()[0] for t in rooted_trees(tuple('abcdefg'[:n]))]
                provenance={};counts['source_tree_count']=len(signatures)
            else:
                signatures,provenance,info=generate_current(n,rho);counts.update(info)
            pairs=[(a,b) for a in signatures for b in signatures]
            full_domain_size=len(pairs)
            if args.limit and len(pairs)>args.limit:
                rng=random.Random(args.seed+100*n+int(rho));rng.shuffle(pairs);pairs=pairs[:args.limit]
            previous=0
            for index,(s1,s2) in enumerate(pairs,1):
                audit_pair(s1,s2,counts,findings,deep=not args.shallow)
                if findings: break
                if index%1000==0:
                    progress('running',f'Executing {args.mode} n={n}, rho={rho}; universal claims open.',dict(counts),[args.receipt,HERE/'evaluator.py',HERE/'search.py',HERE/'WORK.md'])
                    print(json.dumps({'stage':args.mode,'n':n,'rho':rho,'pairs_done':index,'common_subtrees':counts['common_subtree_occurrences'],'seconds':time.perf_counter()-start}),flush=True)
            domain={'n':n,'rho':rho,'full_pair_domain_size':full_domain_size,'exhaustive':len(pairs)==full_domain_size,
                    'counts':dict(counts),'elapsed_seconds':time.perf_counter()-start}
            domains.append(domain)
            receipt=dict(metadata,domains=domains,findings=findings,elapsed_seconds=time.perf_counter()-started,
                         result='FIRE_PENDING_NONAUTHOR_REPLAY' if findings else 'BOUNDED_NO_FIRE')
            atomic_write(args.receipt,receipt)
            print(json.dumps({'completed_domain':domain}),flush=True)
            if findings:
                atomic_write(args.receipt.with_name(args.receipt.stem+'-witness.json'),findings[0]);return receipt
    progress('tested','Bounded X0 search completed; no universal inference.',{'domains':len(domains),'findings':len(findings),'common_subtree_occurrences':sum(d['counts'].get('common_subtree_occurrences',0) for d in domains)},[args.receipt,HERE/'evaluator.py',HERE/'search.py',HERE/'WORK.md'])
    return receipt

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--mode',choices=['whole','current'],required=True)
    parser.add_argument('--max-n',type=int,default=4);parser.add_argument('--limit',type=int,default=0)
    parser.add_argument('--seed',type=int,default=14102026);parser.add_argument('--receipt',type=Path,required=True)
    parser.add_argument('--shallow',action='store_true')
    run(parser.parse_args())
