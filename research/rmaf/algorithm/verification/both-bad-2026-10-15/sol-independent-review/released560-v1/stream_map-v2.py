#!/usr/bin/env python3
"""Bounded-memory JSON string-token hashing; retains full raw scientific map.
JSON syntax/metadata are preserved; only type/body string tokens become SHA256
markers. Standard json validates the resulting small map. No expression omitted.
"""
import hashlib,json,pathlib,time
HERE=pathlib.Path(__file__).resolve().parent

class Stream:
    def __init__(self,f,chunk):self.f=f;self.chunk=chunk;self.buf=b'';self.pos=0;self.bytes=0
    def fill(self):
        if self.pos<len(self.buf):return True
        self.buf=self.f.read(self.chunk);self.bytes+=len(self.buf);self.pos=0
        return bool(self.buf)
    def peek(self):return self.buf[self.pos] if self.fill() else None
    def char(self):
        c=self.peek()
        if c is not None:self.pos+=1
        return c
    def whitespace(self):
        while self.peek() in [9,10,13,32]:self.pos+=1
    def string(self,capture):
        assert self.char()==34
        h=hashlib.sha256();h.update(b'"');pieces=[b'"'] if capture else None
        prior_slashes=0
        while True:
            assert self.fill(),'unterminated JSON string'
            start=self.pos;scan=start
            while True:
                q=self.buf.find(b'"',scan)
                if q<0:break
                j=q-1
                while j>=start and self.buf[j]==92:j-=1
                slashes=q-1-j+(prior_slashes if j<start else 0)
                if slashes%2==0:
                    segment=self.buf[start:q+1];h.update(segment)
                    if capture:pieces.append(segment)
                    self.pos=q+1
                    raw=b''.join(pieces) if capture else None
                    if raw is not None:assert len(raw)<(1<<22),'unexpected huge metadata string'
                    return h.hexdigest(),raw
                scan=q+1
            segment=self.buf[start:];h.update(segment)
            if capture:pieces.append(segment)
            j=len(segment)-1
            while j>=0 and segment[j]==92:j-=1
            trailing=len(segment)-1-j
            prior_slashes=trailing+(prior_slashes if trailing==len(segment) else 0)
            self.pos=len(self.buf)

def dehydrate(source,destination,chunk=1<<20):
    count=0;started=time.perf_counter();pending=False
    with source.open('rb') as f,destination.open('wb') as out:
        s=Stream(f,chunk)
        while True:
            s.whitespace();c=s.peek()
            if c is None:break
            if c==34:
                digest,raw=s.string(capture=not pending)
                if pending:
                    out.write(json.dumps('RAW_JSON_TOKEN_SHA256:'+digest).encode());count+=1;pending=False
                    s.whitespace()
                    assert s.peek()!=58,'body/type value unexpectedly used as key'
                else:
                    out.write(raw);s.whitespace()
                    if s.peek()==58:
                        key=json.loads(raw)
                        pending=key in ['body','type']
                continue
            if pending and c!=58:
                assert c==110,'body/type field must be string or null'
                count+=1;pending=False
            out.write(bytes([s.char()]))
        out.write(b'\n')
    data=json.loads(destination.read_text())
    return {'source_bytes':s.bytes,'digest_fields':count,'seconds':time.perf_counter()-started,
            'destination_bytes':destination.stat().st_size},data

def plants():
    obj={'records':[{'name':'known','body':'A\\B\n"quote"'+'x'*10000,'type':'Nat'},
                    {'name':'null','body':None,'type':'True'}]}
    src=HERE/'stream-positive-v2.json';src.write_text(json.dumps(obj,indent=2)+'\n')
    record,got=dehydrate(src,HERE/'stream-positive-digest-v2.json',chunk=128)
    expected=json.loads(json.dumps(obj))
    for row in expected['records']:
        for k in ['body','type']:
            if row[k] is not None:row[k]='RAW_JSON_TOKEN_SHA256:'+hashlib.sha256(json.dumps(row[k]).encode()).hexdigest()
    assert got==expected and record['digest_fields']==4
    bad=json.loads(json.dumps(obj));bad['records'][0]['body']='corrupted'
    srcbad=HERE/'stream-corruption-v2.json';srcbad.write_text(json.dumps(bad,indent=2)+'\n')
    _,corrupt=dehydrate(srcbad,HERE/'stream-corruption-digest-v2.json',chunk=128)
    assert corrupt!=expected
    toy=HERE.parent/'toys/AuditProducerFull-stored.json'
    r,b=dehydrate(toy,HERE/'stream-toy-digest-v2.json',chunk=1024)
    a=json.loads(toy.read_text())
    assert len(a['stored_occurrences'])==len(b['stored_occurrences'])==33
    for key in ['stored_occurrences','resolved_names']:
        for x,y in zip(a[key],b[key]):
            assert {k:v for k,v in x.items() if k not in ['body','type']}=={k:v for k,v in y.items() if k not in ['body','type']}
    assert r['digest_fields']==132
    return {'positive_exact_token_hash':True,'corruption_caught':True,'toy_occurrences_preserved':33}

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['plants','pilot','full']);args=ap.parse_args()
    if args.mode=='plants':receipt=plants()
    else:
        name='AuditPilot' if args.mode=='pilot' else 'AuditScientific'
        receipt,_=dehydrate(HERE/(name+'.json'),HERE/(name+'-digest-v2.json'))
    (HERE/('stream-'+args.mode+'-receipt-v2.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt))
