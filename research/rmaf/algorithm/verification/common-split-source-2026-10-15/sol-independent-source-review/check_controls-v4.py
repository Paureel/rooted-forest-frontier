#!/usr/bin/env python3
"""Fresh streaming producer gate and fabricated-control comparator.
No candidate paths or theorem bodies are read. Stored records precede resolution.
"""
import copy,hashlib,json,pathlib,collections
P=pathlib.Path(__file__).resolve().parent
ALLOWED={'propext','Classical.choice','Quot.sound'}
CHILDREN={'bvar':(), 'fvar':(), 'mvar':(), 'sort':(), 'const':(), 'app':(1,2), 'lam':(2,3), 'forall':(2,3), 'let':(2,3,4), 'nat':(), 'string':(), 'mdata':(2,), 'proj':(3,)}

def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()
def digest(v):return hashlib.sha256(v).hexdigest()
def read_rows(path):
    with path.open() as f:
        for line in f:
            yield json.loads(line)
def validate_dag(nodes,roots):
    if not nodes:raise ValueError('empty expression DAG')
    seen=set()
    for i,node in enumerate(nodes):
        if not isinstance(node,list) or not node or node[0] not in CHILDREN:raise ValueError('unknown expression tag')
        for pos in CHILDREN[node[0]]:
            c=node[pos]
            if type(c)is not int or c<0 or c>=i:raise ValueError('invalid/nonprecedent child reference')
        k=canonical(node)
        if k in seen:raise ValueError('duplicate structural node')
        seen.add(k)
    for r in roots:
        if r is not None and (type(r)is not int or not 0<=r<len(nodes)):raise ValueError('invalid root index')

def roundtrip(nodes,roots):
    # Explicit DAG->structural-tree->DAG inverse on synthetic tiny controls only.
    def expand(i):
        node=copy.deepcopy(nodes[i])
        for pos in CHILDREN[node[0]]:node[pos]=expand(node[pos])
        return node
    trees=[expand(i) for i in roots]
    out=[];seen={}
    def contract(node):
        node=copy.deepcopy(node)
        for pos in CHILDREN[node[0]]:node[pos]=contract(node[pos])
        key=canonical(node)
        if key not in seen:seen[key]=len(out);out.append(node)
        return seen[key]
    rr=[contract(t) for t in trees]
    if out!=nodes or rr!=roots:raise ValueError('roundtrip representation drift')

def gate(rows):
    parts={};counts=collections.Counter();keys=set();issues=[];occs=[];modules={}
    for row in rows:
        kind=row['record']
        if kind=='module':modules[row['module']]=row
        elif kind=='producer_part':
            k=(row['producer'],row['part'])
            if k in parts:raise ValueError('duplicate producer-part header')
            parts[k]=row
        elif kind=='occurrence':
            k=(row['producer'],row['part'],row['index'])
            if k in keys:raise ValueError('duplicate stored occurrence')
            keys.add(k);counts[k[:2]]+=1;occs.append(row)
            if k[:2] not in parts:raise ValueError('occurrence without producer-part header')
            if row['index'] not in range(parts[k[:2]]['occurrences']):raise ValueError('out-of-range occurrence')
            s=row['stored'];roots=[s['type_root'],s['body_root']]+[r[2] for r in s['rule_roots']]
            validate_dag(s['nodes'],roots)
            if s['name_text']!=row['stored_name']:raise ValueError('name mapping mismatch')
            if s['kind']=='axiom':issues.append((row['producer'],row['stored_name'],'direct custom scientific axiom'))
            if s['unsafe'] or s['partial']:issues.append((row['producer'],row['stored_name'],'unsafe/partial scientific declaration'))
            cl=row['closure']
            for field in ('missing','unsafe','partial'):
                if cl[field]:issues.append((row['producer'],row['stored_name'],'closure '+field+':'+str(cl[field])))
            if set(cl['axioms'])-ALLOWED:issues.append((row['producer'],row['stored_name'],'disallowed axioms:'+str(cl['axioms'])))
            if row['resolved'] is None or row['resolved_origin'] not in modules:issues.append((row['producer'],row['stored_name'],'missing resolved source origin'))
            elif s!=row['resolved']:issues.append((row['producer'],row['stored_name'],'stored/resolved declaration mismatch'))
    for key,h in parts.items():
        if counts[key]!=h['occurrences']:raise ValueError('missing stored occurrence')
        producer=h['producer'];m=modules.get(producer)
        if not m or not m['requested']:raise ValueError('missing producer module mapping')
        if pathlib.Path(h['path']).resolve() != pathlib.Path(m['olean_parts'][h['part']]).resolve():raise ValueError('producer part path mismatch')
        if pathlib.Path(m['olean_parts'][0]).resolve() != (P/'controls'/(producer+'.olean')).resolve():raise ValueError('source/olean path mapping mismatch')
    return {'occurrences':len(occs),'producer_parts':len(parts),'issues':issues,'compiler_extra_names':sum(len(p['compiler_extra_names']) for p in parts.values())},occs

def expect_failure(label,fn):
    try:fn()
    except (ValueError,AssertionError,KeyError,IndexError) as e:return {'control':label,'caught':str(e)}
    raise AssertionError('negative control escaped: '+label)

def equal(actual,expected,reason):
    if actual!=expected:raise ValueError(reason)

def main():
    results={};by={};allrows={}
    for label in ('clean','twins','coalesced','axiom','unsafe','sorry'):
        rows=list(read_rows(P/(label+'-v4.jsonl')));allrows[label]=rows
        result,occ=gate(rows);results[label]=result;by[label]=occ
        expected_clean=label in ('clean','twins')
        assert bool(result['issues'])!=expected_clean,(label,result)
        enc=rows[0]['value'];assert enc['expected_distinct_roots']==20 and len(set(enc['roots']))==20 and enc['name_display_collision'] is True
        validate_dag(enc['nodes'],enc['roots']);roundtrip(enc['nodes'],enc['roots'])
        assert set(n[0] for n in enc['nodes'])==set(CHILDREN)
    clean=by['clean'];named={r['stored_name']:r for r in clean}
    expected_kinds={'ProducerControl.shared':'theorem','ProducerControl.own':'theorem','ProducerControl.seven':'definition','ProducerControl.Mini':'inductive','ProducerControl.Mini.a':'constructor','ProducerControl.Mini.b':'constructor','ProducerControl.Mini.rec':'recursor','ProducerDiagnostic.possible':'theorem'}
    for name,kind in expected_kinds.items():assert named[name]['stored']['kind']==kind
    private=[r for r in clean if r['stored_name'].startswith('_private.') and r['stored_name'].endswith('.ProducerControl.hidden')]
    assert len(private)==1 and private[0]['stored']['kind']=='theorem'
    twins=[r for r in by['twins'] if r['stored_name']=='ProducerControl.shared']
    assert len(twins)==2 and {r['producer'] for r in twins}=={'CleanBase','CleanTwin'}
    assert len({r['resolved_origin'] for r in twins})==1 and all(r['stored']==r['resolved'] for r in twins)
    coal=[r for r in by['coalesced'] if r['stored_name']=='ProducerControl.shared']
    assert len(coal)==2 and {r['stored']['kind'] for r in coal}=={'axiom','theorem'}
    assert {r['resolved']['kind'] for r in coal}=={'theorem'}
    # Show the resolved-kind-only check's false negative, rather than hiding it.
    assert all(r['resolved']['kind']!='axiom' for r in by['coalesced'])
    hostile=[r for r in by['axiom'] if r['stored']['kind']=='axiom']
    assert len(hostile)==2
    assert sum(r['stored_name'].startswith('_private.') and r['stored_name'].endswith('.ProducerHostile.hiddenFalse') for r in hostile)==1
    impossible=[r for r in by['axiom'] if r['stored_name']=='ProducerHostile.impossible'][0]
    assert set(impossible['closure']['axioms']) & {r['stored_name'] for r in hostile}
    assert any(r['stored']['unsafe'] for r in by['unsafe'])
    assert any('sorryAx' in r['closure']['axioms'] for r in by['sorry'])
    badlog=(P/'compile-FalseDiagnostic-v4.log').read_text();assert 'error' in badlog and 'True' in badlog and 'False' in badlog
    negatives=[];baseline=allrows['clean']
    ix=next(i for i,r in enumerate(baseline) if r['record']=='occurrence' and r['stored_name']=='ProducerControl.shared')
    original=baseline[ix]
    for label,action in [
      ('missing_occurrence',lambda z:z.pop(ix)),
      ('duplicate_occurrence',lambda z:z.append(copy.deepcopy(z[ix]))),
      ('altered_kind',lambda z:z[ix]['stored'].__setitem__('kind','axiom')),
      ('altered_type',lambda z:z[ix]['stored']['nodes'][z[ix]['stored']['type_root']].__setitem__(0,'mvar')),
      ('altered_body',lambda z:z[ix]['stored'].__setitem__('body_root',z[ix]['stored']['type_root'])),
      ('altered_import',lambda z:next(r for r in z if r['record']=='producer_part')['imports'].append('ForeignImport')),
      ('altered_producer',lambda z:z[ix].__setitem__('producer','ForeignProducer')),
      ('altered_resolved_origin',lambda z:z[ix].__setitem__('resolved_origin','ForeignOrigin')),
      ('altered_structural_name',lambda z:z[ix]['stored']['name'].append('corrupt')),
      ('altered_levels',lambda z:z[ix]['stored']['levels'].append(['anonymous'])),
    ]:
        changed=copy.deepcopy(baseline);action(changed)
        negatives.append(expect_failure(label,lambda:equal(changed,baseline,'exact occurrence/import/type/body/origin adaptation mismatch')))
        if label in ('missing_occurrence','duplicate_occurrence','altered_producer'):
            negatives.append(expect_failure(label+'_structural_gate',lambda:gate(changed)))
    # Kind-specific recursor RHS and binder/metadata changes must change exact bytes.
    rec=next(r for r in clean if r['stored_name']=='ProducerControl.Mini.rec')
    assert rec['stored']['rule_roots']
    changed=copy.deepcopy(rec);changed['stored']['rule_roots'][0][1]+=1
    negatives.append(expect_failure('altered_recursor_rule',lambda:equal(changed,rec,'exact recursor-rule adaptation mismatch')))
    enc=baseline[0]['value'];changed=copy.deepcopy(enc);changed['nodes'][enc['roots'][0]][1]=['anonymous']
    negatives.append(expect_failure('altered_binder_metadata',lambda:equal(changed,enc,'binder metadata drift')))
    for label,path in [('altered_source_bytes',P/'controls/CleanBase.lean'),('altered_olean_bytes',P/'controls/CleanBase.olean')]:
        raw=path.read_bytes();expected=digest(raw);assert digest(raw)==expected
        negatives.append(expect_failure(label,lambda:equal(digest(raw+b' '),expected,'exact source/olean byte hash mismatch')))
    negatives.append(expect_failure('unsupported_expr_constructor',lambda:validate_dag([['unknown']], [0])))
    # Exact source imports/olean origins and trusted installed binaries, bounded metadata only.
    pins=[];seen=set()
    for rows in allrows.values():
        for row in rows:
            if row['record']=='module':
                for fn in row['olean_parts']:
                    q=pathlib.Path(fn).resolve()
                    if str(q) in seen:continue
                    seen.add(str(q));pins.append({'path':str(q),'sha256':digest(q.read_bytes()),'scope':'own fabricated scientific control' if q.is_relative_to(P/'controls') else 'installed trusted standard-library artifact; not rebuilt'})
    sourcepins=[{'path':str(q.resolve()),'sha256':digest(q.read_bytes())} for q in sorted((P/'controls').glob('*.lean'))]
    out={'status':'PRERELEASE_DETECTOR_CONTROLS_PASS_NOT_CANDIDATE_ACCEPTANCE','schema':'producer-dag-v1','results':results,'clean_named_expectations':expected_kinds,'private_theorem_occurrences':len(private),'stored_shared_occurrences':len(twins),'resolved_shared_names':1,'coalesced_bad_detected_before_resolution':True,'resolved_kind_only_gate_false_negative_demonstrated':True,'encoder_distinct_roots':20,'expression_tags':sorted(CHILDREN),'negative_adaptation_catches':negatives,'source_pins':sourcepins,'trusted_and_control_olean_pins':pins,'limits':['cached Expr/Level bitfields and physical sharing excluded','compiler-only extra names inventoried; bodies unavailable here','installed standard library pins trusted rather than rebuilt','same agent/own X0 reuse yields zero extra mathematical replication credit']}
    (P/'CONTROL-RESULTS-v4.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:out[k] for k in ('status','results','private_theorem_occurrences','stored_shared_occurrences','resolved_shared_names','coalesced_bad_detected_before_resolution','encoder_distinct_roots')},sort_keys=True))
    print('exact-adaptation catches',len(negatives),'pinned olean parts',len(pins))
if __name__=='__main__':main()
