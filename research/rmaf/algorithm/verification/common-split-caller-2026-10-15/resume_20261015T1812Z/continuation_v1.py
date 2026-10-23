#!/usr/bin/env python3
"""One-shot continuation receipts. Same predecessor instrument, zero replication.

Stream full decoded Expr strings to SHA256; raw evidence is always retained.
This file is deliberately task-local because it implements this frozen schema.
"""
import argparse, collections, copy, gzip, hashlib, importlib.util, json, os
from pathlib import Path
import re, selectors, shutil, signal, subprocess, time

P=Path(__file__).resolve().parent
ROOT=P.parents[5]
PRE=P.parent/'sol-caller-main'
POST=PRE/'postrelease-v1'
M=ROOT/'research/rmaf/algorithm/universal233/rule5_common_split_caller/COMMON-SPLIT-CALLER-MANIFEST-v1.json'
LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
BIG={'type','body','resolved_type','resolved_body','rhs'}
EXTRAS={k+'_sha256' for k in ('type','body','recursor_rules','resolved_type','resolved_body','resolved_recursor_rules')}
ALLOW={'propext','Classical.choice','Quot.sound'}

def sha(f):
    h=hashlib.sha256()
    with open(f,'rb') as z:
        for b in iter(lambda:z.read(4*1024*1024),b''):h.update(b)
    return h.hexdigest()

def write(name,obj):
    f=P/name
    if f.exists():raise ValueError('new receipt already exists: '+name)
    f.write_text(json.dumps(obj,indent=2)+'\n')

class Reader:
    """Small streaming JSON reader; complete strings hashed, never truncated."""
    special=re.compile(r'["\\\x00-\x1f]')
    def __init__(self,f):self.f=f;self.buf='';self.i=0
    def more(self):
        self.buf=self.buf[self.i:]+self.f.read(1024*1024);self.i=0
    def peek(self):
        if self.i==len(self.buf):self.more()
        return self.buf[self.i:self.i+1]
    def take(self):
        c=self.peek()
        if not c:raise ValueError('unexpected EOF')
        self.i+=1;return c
    def ws(self):
        while self.peek() and self.peek().isspace():self.i+=1
    def expect(self,c):
        self.ws()
        if self.take()!=c:raise ValueError('expected '+c)
    def string(self,big=False):
        self.expect('"');h=hashlib.sha256();n=0;parts=[]
        def push(s):
            nonlocal n
            if big:b=s.encode();h.update(b);n+=len(b)
            else:parts.append(s)
        while True:
            if not self.peek():raise ValueError('unterminated string')
            m=self.special.search(self.buf,self.i)
            if m is None:
                push(self.buf[self.i:]);self.i=len(self.buf);continue
            push(self.buf[self.i:m.start()]);self.i=m.start();c=self.take()
            if c=='"':return {'decoded_utf8_sha256':h.hexdigest(),'decoded_utf8_bytes':n} if big else ''.join(parts)
            if c!='\\':raise ValueError('control char in JSON string')
            c=self.take()
            if c=='u':
                raw='\\u'+''.join(self.take() for _ in range(4));code=int(raw[2:],16)
                if 0xD800<=code<=0xDBFF:
                    raw+=''.join(self.take() for _ in range(6))
                push(json.loads('"'+raw+'"'))
            else:push({'"':'"','\\':'\\','/':'/','b':'\b','f':'\f','n':'\n','r':'\r','t':'\t'}[c])
    def value(self,key=None):
        self.ws();c=self.peek()
        if c=='"':return self.string(key in BIG)
        if c=='{':
            self.take();o={};self.ws()
            if self.peek()=='}':self.take();return o
            while True:
                k=self.string();self.expect(':');o[k]=self.value(k);self.ws();s=self.take()
                if s=='}':return o
                if s!=',':raise ValueError('object separator')
        if c=='[':
            self.take();o=[];self.ws()
            if self.peek()==']':self.take();return o
            while True:
                o.append(self.value());self.ws();s=self.take()
                if s==']':return o
                if s!=',':raise ValueError('array separator')
        atom=''
        while self.peek() and self.peek() not in ',]} \n\r\t':atom+=self.take()
        return json.loads(atom)

def project(f):
    op=gzip.open if str(f).endswith('.gz') else open
    with op(f,'rt',encoding='utf-8') as z:
        r=Reader(z);d=r.value();r.ws()
        if r.peek():raise ValueError('trailing JSON bytes')
    for row in d.get('rows',[]):
        for k in EXTRAS:row.pop(k,None)
    return d

def gate(d,modules,imports=None):
    if d['trustLevel']!=0:raise ValueError('trust level')
    hs=d['producers'];rows=d['rows'];loaded=set(d['loaded_modules'])
    if len(hs)!=len(modules) or {h['module'] for h in hs}!=set(modules):raise ValueError('producer coverage')
    keys=[(r['producer'],r['index'],r['name']) for r in rows]
    if len(keys)!=len(set(keys)):raise ValueError('duplicate occurrence')
    if {r['producer'] for r in rows}!={h['module'] for h in hs if h['count']}:raise ValueError('row coverage')
    for h in hs:
        if type(h['count'])is not int or h['count']<0:raise ValueError('count')
        if sorted(r['index'] for r in rows if r['producer']==h['module'])!=list(range(h['count'])):raise ValueError('occurrence indices')
        if imports is not None and h['imports']!=imports[h['module']]:raise ValueError('stored import')
    owners=collections.defaultdict(set)
    for r in rows:owners[r['name']].add(r['producer'])
    proofdiff=[];partial=[];unsafe=[]
    for r in rows:
        if not r['type'] or r['type']['decoded_utf8_bytes']==0 or r['missing']:raise ValueError('type/missing reference')
        if r['resolved_origin'] not in loaded or r['resolved_type'] is None:raise ValueError('unresolved origin')
        if 'Caller' in r['name'] and r['resolved_origin'] not in owners[r['name']]:raise ValueError('caller origin')
        if r['kind'] in {'theorem','definition','opaque'} and r['body'] is None:raise ValueError('body absent')
        if r['resolved_kind'] in {'theorem','definition','opaque'} and r['resolved_body'] is None:raise ValueError('resolved body absent')
        if r['kind']=='axiom' and r['name'] not in ALLOW:raise ValueError('direct custom axiom '+r['producer']+':'+r['name'])
        if set(r['axioms'])-ALLOW:raise ValueError('custom axiom closure')
        if r['kind']!=r['resolved_kind'] or r['type']!=r['resolved_type']:raise ValueError('kind/type incompatibility '+r['name'])
        if r['body']!=r['resolved_body'] or r['recursor_rules']!=r['resolved_recursor_rules']:
            if r['kind']=='theorem':proofdiff.append([r['producer'],r['name']])
            else:raise ValueError('nonproof body/rules incompatibility '+r['name'])
        if r['partial']:partial.append([r['producer'],r['name']])
        if r['unsafe']:unsafe.append([r['producer'],r['name']])
    return {'proof_body_differences':proofdiff,'partial_occurrences':partial,'unsafe_occurrences':unsafe,
            'kind_counts':dict(collections.Counter(r['kind'] for r in rows)),
            'axiom_union':sorted({a for r in rows for a in r['axioms']})}

def pins():
    rows=[]
    for f in [Path(__file__),POST/'CallerProducerAudit_chunk_v3.lean',POST/'build_exact_v1.py',POST/'build_exact_v2.py',POST/'run_readouts_v4.py',POST/'audit_chunks_v3.py',POST/'audit_exact_v2.py',PRE/'origin_gate_v2.py',ROOT/'research/rmaf/algorithm/verification/cherry-branch-2026-10-15/sol-main-necessity/origin_gate_v3.py',POST/'Readouts_v3.lean',POST/'Readouts_pilot_v2.lean',POST/'generate_readouts_v3.py',POST/'case_inputs_v3.py',POST/'readouts-full-v4.json']:
        rows.append({'path':str(f.relative_to(ROOT)),'sha256':sha(f),'bytes':f.stat().st_size})
    write('INSTRUMENT-REUSE-PINS-v1.json',{'same_lineage':True,'replication_credit':0,'files':rows})

def integrity():
    at=time.perf_counter();checks=[]
    def members(f,expected,groups):
        assert sha(f)==expected
        d=json.loads(f.read_text())
        for group in groups:
            for r in d[group]:
                z=ROOT/r['path'];assert z.stat().st_size==r['bytes'] and sha(z)==r['sha256'],r['path']
            checks.append({'manifest':str(f.relative_to(ROOT)),'group':group,'matched':len(d[group])})
        return d
    members(P.parent/'ROOT-RELEASE-v1.json','baa70f84f0974e2f5767876cde7d846e61f8eb8f08ac7c8981226c3ea9d69f47',[])
    members(PRE/'READY-MANIFEST-v1.json','ffc6fe9b3c30f85f121979cc2b8a5492be2d7477d0863b9d7405adad927441d8',['files','permitted_inputs'])
    members(M,'3da4d51890af8e552b9942667f0f61afff9f6def6af58073f8f1d05286f1714e',['immutable_files','external_input_pins'])
    inv=json.loads((POST/'integrity-pilot-v1.json').read_text());order=json.loads((POST/'source-order-v1.json').read_text());by={r['module']:r for r in inv['sources']}
    reports=[json.loads((POST/f'build-{m}-v1.json').read_text())for m in ['pilot','full']]
    records=sum([r['commands']for r in reports],[]);assert [r['module']for r in records]==order and len(order)==173
    bins=[];done=set()
    for rep,script in zip(reports,['build_exact_v1.py','build_exact_v2.py']):
        assert rep['status']=='PASS' and rep['lean_binary_sha256']==sha(LEAN) and rep['script_sha256']==sha(POST/script)
    for r in records:
        n=r['module'];s=POST/'scientific-src'/(n+'.lean');b=POST/'scientific-build'/(n+'.olean');log=POST/r['log']
        assert sha(s)==by[n]['sha256']==sha(ROOT/by[n]['source'])
        assert r['returncode']==0 and r['cwd']==str(s.parent) and r['LEAN_PATH']==str(b.parent)
        assert r['command']==[str(LEAN),'-o',str(b),n+'.lean'] and b.exists() and log.exists()
        assert all(i in done or i in {'Init','Std','Lean'}for i in by[n]['imports'])
        artifacts=[{'path':str(f.relative_to(ROOT)),'bytes':f.stat().st_size,'sha256':sha(f)}for f in b.parent.glob(n+'.*')]
        bins.append({'module':n,'source_sha256':sha(s),'log_sha256':sha(log),'log_bytes':log.stat().st_size,'artifacts':artifacts});done.add(n)
    write('INTEGRITY-BUILD-CORRESPONDENCE-v1.json',{'status':'MATCH','checks':checks,'source_count':173,'build_commands':173,'current_artifacts':bins,'seconds':time.perf_counter()-at,'scope':'same-lineage cold-build commands, exact source copies and present outputs/logs; current output hashes pinned now, no historical output hash invented; installed Lean/Std trusted; no rebuild repeated'})
    print(json.dumps({'integrity':'MATCH','checks':checks,'build_commands':173,'seconds':time.perf_counter()-at}))

def controls():
    import io
    at=time.perf_counter();results=[]
    # Chunk boundaries, all JSON escapes, Unicode/surrogates, missing/trailing.
    class Tiny(io.StringIO):
        def read(self,n=-1):return super().read(min(n,7))
    for s in ['plain','a"b\\c\n\t\b\f\r/','α😀','x'*300]:
        t=json.dumps({'type':s,'body':None,'other':s},ensure_ascii=True);r=Reader(Tiny(t));d=r.value()
        assert d['type']=={'decoded_utf8_sha256':hashlib.sha256(s.encode()).hexdigest(),'decoded_utf8_bytes':len(s.encode())}and d['other']==s
    for name in ['origin-full-CallerCleanA-v2.json','origin-full-CallerCleanA+CallerCleanB-v2.json','origin-full-CallerCleanB+CallerCleanA-v2.json','origin-full-CallerGenerated-v2.json','origin-full-CallerEmpty-v2.json']:
        f=PRE/name;raw=json.loads(f.read_text());d=project(f)
        for a,b in zip(raw['rows'],d['rows']):
            for k in ['type','body','resolved_type','resolved_body']:
                assert b[k] is None if a[k] is None else b[k]=={'decoded_utf8_sha256':hashlib.sha256(a[k].encode()).hexdigest(),'decoded_utf8_bytes':len(a[k].encode())}
        ms=[h['module']for h in d['producers']];g=gate(d,ms);results.append({'control':name,'pass':True,'rows':len(d['rows'])})
    base=project(PRE/'origin-full-CallerCleanA-v2.json');ms=['CallerCleanA']
    def reject(name,fn):
        try:fn()
        except (ValueError,AssertionError)as e:results.append({'control':name,'rejected':True,'reason':str(e)})
        else:raise AssertionError('control survived '+name)
    for name,mut in [('missing',lambda d:d['rows'].pop()),('duplicate',lambda d:d['rows'].append(copy.deepcopy(d['rows'][0]))),('header',lambda d:d['producers'].clear()),('unresolved',lambda d:d['rows'][0].update(resolved_origin='MISSING')),('body',lambda d:d['rows'][0].update(body={'decoded_utf8_sha256':'WRONG','decoded_utf8_bytes':1})),('type',lambda d:d['rows'][0].update(type={'decoded_utf8_sha256':'WRONG','decoded_utf8_bytes':1}))]:
        d=copy.deepcopy(base);mut(d);reject(name,lambda:gate(d,ms))
    for name in ['origin-full-CallerUnused-v2.json','origin-full-CallerPrivate-v2.json','origin-full-CallerCleanA+CallerHostile-v2.json','origin-full-CallerHostile+CallerCleanA-v2.json','origin-CallerPrivateClean+CallerPrivateHostile-v2.json','origin-CallerPrivateHostile+CallerPrivateClean-v2.json']:
        d=project(PRE/name);reject(name,lambda:gate(d,[h['module']for h in d['producers']]))
    # Nonproof conflict remains rejection even if a simulated raw/resolved receipt is otherwise clean.
    d=copy.deepcopy(base);rr=next(r for r in d['rows']if r['kind']=='definition');rr['resolved_body']={'decoded_utf8_sha256':'WRONG','decoded_utf8_bytes':1};reject('nonproof incompatible value',lambda:gate(d,ms))
    write('STREAM-CONTROLS-v1.json',{'status':'PASS','postcontact':True,'new_blind_credit':0,'controls':results,'string_tests':4,'seconds':time.perf_counter()-at,'script_sha256':sha(Path(__file__))})
    print(json.dumps({'controls':'PASS','named':len(results),'seconds':time.perf_counter()-at}))

def scan(indices,label):
    assert json.loads((P/'STREAM-CONTROLS-v1.json').read_text())['status']=='PASS'
    start=time.perf_counter();receipts=[];order=json.loads((POST/'source-order-v1.json').read_text())
    for i in indices:
        at=time.perf_counter();j=POST/f'producer-chunk-v3-{i}.json';log=POST/f'producer-chunk-v3-{i}.log'
        dj=project(j);dl=project(log);assert dj==dl,('raw/enriched difference',i)
        assert [h['module']for h in dj['producers']]==order[i*10:(i+1)*10]
        z={'batch':i,'projection':dj,'raw_json_sha256':sha(j),'raw_log_sha256':sha(log),'raw_json_bytes':j.stat().st_size,'raw_log_bytes':log.stat().st_size,'seconds':time.perf_counter()-at}
        write(f'projected-prior-batch-{i}-v1.json',z);receipts.append({k:v for k,v in z.items()if k!='projection'})
        print(json.dumps(receipts[-1]),flush=True)
    write(label,{'status':'COMPLETE_PROJECTION_ONLY','batches':receipts,'seconds':time.perf_counter()-start,'not_a_gate_pass':True})

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['pins','integrity','controls','scan-pilot','scan-rest']);args=ap.parse_args()
    {'pins':pins,'integrity':integrity,'controls':controls,'scan-pilot':lambda:scan([0],'STREAM-PILOT-v1.json'),'scan-rest':lambda:scan(range(1,15),'STREAM-PRIOR-REST-v1.json')}[args.mode]()
