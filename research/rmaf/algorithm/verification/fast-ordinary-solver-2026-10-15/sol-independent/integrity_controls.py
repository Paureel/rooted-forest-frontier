#!/usr/bin/env python3
"""One-campaign full stored-row audit and planted source/producer integrity controls.

Only reads own compressed evidence, own Lean artifacts, and explicitly pinned runtime.
The lock is a data-integrity baseline, not a mathematical truth generator. Proof
reference extraction trusts the reviewed pinned stored producer and Lean runtime.
"""
import copy, gzip, hashlib, json, pathlib, sys

HERE=pathlib.Path(__file__).resolve().parent
RUNTIME=HERE.parents[5]/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0'

def digest(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def rowhash(r):return hashlib.sha256(canonical(r)).hexdigest()

def evidence(label):
    records=[]
    for p in (HERE/'evidence').glob('*.json'):
        v=json.loads(p.read_text())
        if v['label']==label:records.append((p,v))
    if len(records)!=1:raise ValueError(('evidence denominator',label,len(records)))
    p,v=records[0];raw=b''
    for shard in v['shards']:
        sp=HERE/shard['path']
        if digest(sp)!=shard['sha256']:raise ValueError('shard pin')
        with gzip.open(sp,'rb') as f:
            while True:
                chunk=f.read(65536)
                if not chunk:break
                raw+=chunk
                if len(raw)>64*1024**2:raise ValueError('raw cap')
    if len(raw)!=v['raw_bytes']:raise ValueError('raw count')
    if any(len(line)>16*1024**2 for line in raw.splitlines()):raise ValueError('line cap')
    return p,v,raw

def produced(label):
    _,v,raw=evidence(label)
    if v['returncode']!=0 or v['stop_reason']:raise ValueError(('producer failed',label))
    rr=[json.loads(line) for line in raw.splitlines()]
    if not rr or rr[0].get('record')!='header':raise ValueError('header')
    return rr

def level(x):
    if not isinstance(x,list) or not x:raise ValueError('level')
    tag=x[0]
    if tag=='zero' and len(x)==1:return
    if tag=='succ' and len(x)==2:level(x[1]);return
    if tag in ('max','imax') and len(x)==3:level(x[1]);level(x[2]);return
    if tag=='param' and len(x)==2 and isinstance(x[1],str):return
    # A kernel body with unresolved metavariables must fail.
    raise ValueError(('unsupported/malformed universe',tag))

def expression(x):
    """Return actual full serialized body references and constructor node count."""
    if not isinstance(x,list) or not x:raise ValueError('truncated expression')
    tag=x[0];refs=set();nodes=1
    def child(v):
        nonlocal nodes
        r,n=expression(v);refs.update(r);nodes+=n
    if tag=='const' and len(x)==3 and isinstance(x[1],str) and isinstance(x[2],list):
        for u in x[2]:level(u)
        refs.add(x[1])
    elif tag=='sort' and len(x)==2:level(x[1])
    elif tag=='bvar' and len(x)==2 and type(x[1]) is int and x[1]>=0:pass
    elif tag=='nat' and len(x)==2 and type(x[1]) is int and x[1]>=0:pass
    elif tag=='str' and len(x)==2 and isinstance(x[1],str):pass
    elif tag=='app' and len(x)==3:child(x[1]);child(x[2])
    elif tag in ('lam','forall') and len(x)==5 and isinstance(x[1],str) and isinstance(x[4],str):
        child(x[2]);child(x[3])
    elif tag=='let' and len(x)==6 and isinstance(x[1],str) and type(x[5]) is bool:
        child(x[2]);child(x[3]);child(x[4])
    elif tag=='proj' and len(x)==4 and isinstance(x[1],str) and type(x[2]) is int:
        refs.add(x[1]);child(x[3])
    elif tag=='metadata' and len(x)==3:
        # Repr data is retained, but arbitrary Syntax-valued metadata is not yet
        # calibrated. Refuse instead of claiming a full semantic serialization.
        raise ValueError('metadata body unsupported pending exact encoder calibration')
    else:raise ValueError(('unsupported/malformed expression',tag))
    return refs,nodes

def rows(rr,expected=None):
    header=rr[0];decls=[r for r in rr[1:] if 'record' not in r]
    external=[r for r in rr[1:] if r.get('record')=='external-trust-boundary']
    if len(decls)!=header['count'] or not decls:raise ValueError('missing/zero rows')
    if any(r.get('record') not in (None,'external-trust-boundary') for r in rr[1:]):raise ValueError('unknown row')
    names=[r['name'] for r in decls]
    if len(names)!=len(set(names)):raise ValueError('duplicate declaration rows')
    externals={r['name']:r for r in external}
    if len(externals)!=len(external):raise ValueError('duplicate external rows')
    if header['import_level']!='private':raise ValueError('private imports required')
    all_refs=set();walked=0;proofs=0;recursor_rules=0
    for r in decls:
        if r['module'] not in header['modules']:raise ValueError('module provenance')
        tr,tn=expression(r['type']);walked+=tn
        if tr!=set(r['type_refs']):raise ValueError('type dependency mismatch')
        k=r['kind'];body=r['body'];payload=r['data_payload'];extra=set()
        fields={
            'definition':{'safety','hints','all'},'theorem':{'all'},'opaque':{'all'},'axiom':set(),
            'inductive':{'all','ctors','numParams','numIndices','numNested','isRec','isReflexive'},
            'constructor':{'induct','cidx','numParams','numFields'},
            'recursor':{'all','numParams','numIndices','numMotives','numMinors','k','rules'},
            'quotient':{'quotKind'}}
        if k not in fields or set(payload)!=fields[k]:raise ValueError('incomplete nonproof data payload')
        if k in ('definition','opaque'):
            if body is None or r['proof_body_omitted_after_actual_walk']:raise ValueError('nonproof body missing')
            br,bn=expression(body);walked+=bn
            if br!=set(r['body_refs']) or bn!=r['body_nodes']:raise ValueError('body walk mismatch')
        elif k=='theorem':
            if body is not None or not r['proof_body_omitted_after_actual_walk'] or r['body_nodes']<1:
                raise ValueError('proof body actual-walk attestation')
            proofs+=1
        elif body is not None or r['body_nodes']!=0 or r['body_refs']:
            raise ValueError('unexpected body')
        if k=='inductive':extra.update(payload['all']);extra.update(payload['ctors'])
        elif k=='constructor':extra.add(payload['induct'])
        elif k=='recursor':
            extra.update(payload['all'])
            for rule in payload['rules']:
                if set(rule)!={'ctor','nfields','rhs'}:raise ValueError('recursor rule payload')
                rr0,nn=expression(rule['rhs']);extra.update(rr0);extra.add(rule['ctor']);walked+=nn;recursor_rules+=1
        if extra!=set(r['extra_refs']):raise ValueError('extra dependency mismatch')
        all_refs.update(tr);all_refs.update(r['body_refs']);all_refs.update(extra)
    if all_refs-set(names)-set(externals):raise ValueError('unknown declaration reference')
    if set(externals)-all_refs:raise ValueError('extraneous trust boundary')
    for name,r in externals.items():
        # Name prefixes alone are insufficient. Resolve every recorded trusted
        # module to the pinned installed runtime, with no project lookup.
        if not r['module'].startswith(('Init.','Lean.','Std.')) and r['module'] not in ('Init','Lean','Std'):
            raise ValueError('unlicensed external module')
        p=RUNTIME/'lib/lean'/pathlib.Path(*r['module'].split('.')).with_suffix('.olean')
        if not p.is_file() or not p.resolve().is_relative_to(RUNTIME.resolve()):raise ValueError('external binary path')
    if expected is not None:
        actual={r['name']:rowhash(r) for r in decls}
        if actual!=expected:raise ValueError('missing/altered row commitment')
    return {r['name']:r for r in decls},{'rows':len(decls),'full_expression_nodes_walked':walked,
        'proofs_actual_walk_attested':proofs,'recursor_rules_walked':recursor_rules,'trusted_external_names':len(externals)}

def axiom_closure(decls,start):
    seen=set();todo=[start];axioms=set()
    while todo:
        name=todo.pop()
        if name in seen or name not in decls:continue
        seen.add(name);r=decls[name]
        if r['kind']=='axiom':axioms.add(name)
        todo.extend(r['type_refs']+r['body_refs']+r['extra_refs'])
    return axioms

def source_gate(decls):
    failures=[]
    for name,r in decls.items():
        if r['kind']=='axiom':failures.append(('custom-axiom',name))
        if r['unsafe'] or r['partial']:failures.append(('unsafe-or-partial',name))
        if any(dep=='sorryAx' or dep.endswith('.sorryAx') for dep in r['type_refs']+r['body_refs']+r['extra_refs']):
            failures.append(('sorryAx',name))
    if failures:raise ValueError(failures)
    return True

def artifact_roles():
    out=[]
    for m in ('PClean','PAxiom','PData','PDupA','PDupB','Producer'):
        out += [(m+'-source',HERE/'lean'/f'{m}.lean'),(m+'-binary',HERE/'lean'/f'{m}.olean')]
    out += [('stored-invoker-source',HERE/'lean/StoredInvoke.lean'),('compiler',RUNTIME/'bin/lean')]
    return out

def make_lock():
    artifacts=[{'role':role,'path':str(p),'sha256':digest(p),'bytes':p.stat().st_size} for role,p in artifact_roles()]
    rowpins={}
    for label in ('clean-v2','axiom','data','dup-a','dup-b'):
        rr=produced('stored-producer-'+label);ds,_=rows(rr)
        rowpins[label]={name:rowhash(r) for name,r in ds.items()}
    lock={'version':1,'phase':'precontact-own-artifacts-only','artifacts':artifacts,'row_commitments':rowpins,
          'meaning':'integrity baseline only; no algorithm or mathematical acceptance'}
    (HERE/'ARTIFACT-LOCK-v1.json').write_text(json.dumps(lock,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'LOCK-WRITTEN','sha256':digest(HERE/'ARTIFACT-LOCK-v1.json'),'artifacts':len(artifacts)}))

def audit_manifest(manifest,lock):
    given=manifest['artifacts'];expected=lock['artifacts']
    roles=[r['role'] for r in given]
    if len(roles)!=len(set(roles)) or set(roles)!={r['role'] for r in expected}:raise ValueError('missing/duplicate artifact rows')
    expected={r['role']:r for r in expected}
    for row in given:
        pin=expected[row['role']]
        if row['path']!=pin['path']:raise ValueError('wrong source/binary/producer path')
        if row['sha256']!=pin['sha256']:raise ValueError('wrong source/binary/producer hash')
        p=pathlib.Path(row['path'])
        if digest(p)!=pin['sha256'] or p.stat().st_size!=pin['bytes']:raise ValueError('artifact byte drift')

def controls():
    lock=json.loads((HERE/'ARTIFACT-LOCK-v1.json').read_text());caught=[];summary={}
    audit_manifest(copy.deepcopy(lock),lock)
    for role in ('PClean-source','PClean-binary','Producer-source','Producer-binary'):
        for field in ('path','sha256'):
            bad=copy.deepcopy(lock);row=next(r for r in bad['artifacts'] if r['role']==role)
            row[field]=row[field]+'.wrong' if field=='path' else '0'*64
            try:audit_manifest(bad,lock)
            except ValueError:caught.append(role+'-'+field)
            else:raise AssertionError('manifest mutation escaped')
    for label in ('clean-v2','axiom','data','dup-a','dup-b'):
        rr=produced('stored-producer-'+label);ds,info=rows(rr,lock['row_commitments'][label]);summary[label]=info
        for mutation in ('missing','duplicate','unknown-reference','truncated-nonproof','missing-payload'):
            bad=copy.deepcopy(rr)
            idx=next(i for i,r in enumerate(bad) if r.get('kind') in ('definition','opaque'))
            if mutation=='missing':bad.pop(idx)
            elif mutation=='duplicate':bad.append(copy.deepcopy(bad[idx]))
            elif mutation=='unknown-reference':bad[idx]['body_refs'].append('Unlicensed.missing')
            elif mutation=='truncated-nonproof':bad[idx]['body']=[]
            elif mutation=='missing-payload':bad[idx]['data_payload']={}
            try:rows(bad,lock['row_commitments'][label])
            except ValueError:caught.append(label+'-'+mutation)
            else:raise AssertionError('body/row mutation escaped')
    clean,_=rows(produced('stored-producer-clean-v2'))
    if clean['PrecontactClean.consumer']['body_refs']!=['PrecontactClean.helper']:
        raise AssertionError('actual proof-only dependency missing')
    if 'PrecontactClean.helper' in clean['PrecontactClean.consumer']['type_refs']:
        raise AssertionError('proof-only plant is not proof-only')
    source_gate(clean)
    if any(axiom_closure(clean,n) for n in clean):raise AssertionError('clean custom axiom')
    for mutation in ('proof-body-ref-removal','unsafe','partial'):
        bad=copy.deepcopy(produced('stored-producer-clean-v2'))
        target=next(r for r in bad if r.get('name')=='PrecontactClean.consumer')
        if mutation=='proof-body-ref-removal':target['body_refs']=[]
        else:target[mutation]=True
        try:
            if mutation=='proof-body-ref-removal':rows(bad,lock['row_commitments']['clean-v2'])
            else:source_gate(rows(bad)[0])
        except ValueError:caught.append(mutation)
        else:raise AssertionError('proof/source row mutation escaped')
    ax,_=rows(produced('stored-producer-axiom'))
    all_axioms={n for n,r in ax.items() if r['kind']=='axiom'}
    hidden='_private.PAxiom.0.PrecontactAxiom.hidden';unused='_private.PAxiom.0.PrecontactAxiom.neverUsed'
    if all_axioms!={hidden,unused}:raise AssertionError('private/unused inventory')
    if axiom_closure(ax,'PrecontactAxiom.harmless'):raise AssertionError('harmless should not reach planted axioms')
    if axiom_closure(ax,'PrecontactAxiom.opaqueData')!={hidden}:raise AssertionError('opaque stored body hidden dependency')
    try:source_gate(ax)
    except ValueError as e:
        if hidden not in str(e) or unused not in str(e):raise AssertionError('axiom inventory refusal incomplete')
        caught.append('global-private-unused-axiom')
    else:raise AssertionError('custom axiom gate did not reject')
    # Reached independently from the actual full opaque body, not theorem axiom output.
    if axiom_closure(ax,'PrecontactAxiom.opaqueData'):
        caught.append('opaque-hidden-axiom')
    sorry,_=rows(produced('stored-producer-sorry'))
    try:source_gate(sorry)
    except ValueError as e:
        if 'sorryAx' not in str(e):raise AssertionError('wrong sorry refusal')
        caught.append('sorryAx-even-at-trusted-runtime-boundary')
    else:raise AssertionError('sorry proof accepted')
    a,_=rows(produced('stored-producer-dup-a'));b,_=rows(produced('stored-producer-dup-b'))
    shared=set(a)&set(b)
    if shared!={'PrecontactDuplicate.datum'} or a[next(iter(shared))]['body']==b[next(iter(shared))]['body']:
        raise AssertionError('duplicate data plant')
    for label,first,second in [('dup-ab','PDupA','PDupB'),('dup-ba','PDupB','PDupA')]:
        _,v,raw=evidence('stored-producer-'+label)
        expected=f"import {second} failed, environment already contains 'PrecontactDuplicate.datum' from {first}"
        if v['returncode']==0 or v['stop_reason'] is not None or expected.encode() not in raw:
            raise AssertionError('duplicate import order did not reject for exact expected reason')
        caught.append(label+'-duplicate-nonproof')
    for label,mutate in [('missing-artifact',lambda x:x.pop()),('duplicate-artifact',lambda x:x.append(copy.deepcopy(x[0])))]:
        bad=copy.deepcopy(lock);mutate(bad['artifacts'])
        try:audit_manifest(bad,lock)
        except ValueError:caught.append(label)
        else:raise AssertionError('artifact inventory mutation escaped')
    for label,reason in [('guard-clean',None),('guard-raw','raw cap'),('guard-line','line cap'),
                         ('guard-time','time cap'),('guard-launch','No such file or directory')]:
        matches=[json.loads(p.read_text()) for p in (HERE/'evidence').glob('*.json')
                 if json.loads(p.read_text())['label']==label]
        if len(matches)!=1:raise AssertionError('guard denominator')
        v=matches[0]
        if reason is None:
            if v['returncode']!=0 or v['stop_reason']:raise AssertionError('clean guard')
        elif reason not in (v['stop_reason'] or ''):raise AssertionError('guard stop not retained')
        else:caught.append(label+'-stop-retained')
        if v['retained_raw_bytes']>v['effective_caps']['raw']:raise AssertionError('retained raw cap')
    print(json.dumps({'status':'INTEGRITY-CONTROL-PASS','caught_count':len(caught),'caught':caught,
                      'row_audit':summary,'private_axioms':sorted(all_axioms),
                      'proof_text_omitted_only_after_actual_producer_walk':True,
                      'clean_source_binary_producer_paths_hashes_checked':True,
                      'universal_semantic_proof':False,'compiler_runtime_trusted':True},sort_keys=True))

if __name__=='__main__':
    if sys.argv[1]=='lock':make_lock()
    elif sys.argv[1]=='controls':controls()
    else:raise ValueError('mode')
