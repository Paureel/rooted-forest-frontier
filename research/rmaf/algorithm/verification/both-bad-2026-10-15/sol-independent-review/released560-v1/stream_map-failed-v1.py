#!/usr/bin/env python3
"""One-shot bounded-memory digest of own Lean pretty JSON string fields.

Lean repr expands shared expression subterms. The full raw audit is retained;
this reduces each physical-line type/body JSON token to an exact SHA256 marker.
It changes representation only, not source or declaration coverage.
"""
import hashlib,json,pathlib,re,time
HERE=pathlib.Path(__file__).resolve().parent
PREFIX=re.compile(rb'^(\s*"(?:type|body)"\s*:\s*)(.*)$')

def dehydrate(source,destination,chunk=1<<20):
    count=0;total=0;started=time.perf_counter()
    with source.open('rb') as f,destination.open('wb') as out:
        while True:
            line=f.readline(chunk)
            if not line:break
            total+=len(line)
            match=PREFIX.match(line)
            if match:
                prefix,token=match.groups();h=hashlib.sha256();tail=line
                # No literal physical newline is legal within a JSON string.
                while not tail.endswith(b'\n'):
                    h.update(token)
                    tail=f.readline(chunk)
                    assert tail,'unterminated JSON field line'
                    total+=len(tail);token=tail
                token=token.rstrip(b'\r\n\t ')
                comma=token.endswith(b',')
                if comma:token=token[:-1].rstrip()
                h.update(token);count+=1
                if match.group(2).lstrip().startswith(b'null'):
                    assert count and h.hexdigest()==hashlib.sha256(b'null').hexdigest()
                    replacement=b'null'
                else:
                    assert match.group(2).startswith(b'"') and token.endswith(b'"'), 'unsupported pretty JSON layout'
                    replacement=json.dumps('RAW_JSON_TOKEN_SHA256:'+h.hexdigest()).encode()
                out.write(prefix+replacement+(b',' if comma else b'')+b'\n')
            else:
                # Metadata field lines must fit the bounded chunk. Refuse any
                # unrecognized huge scalar rather than silently truncating it.
                assert line.endswith(b'\n'), 'unrecognized long metadata line'
                out.write(line)
    return {'source_bytes':total,'digest_fields':count,'seconds':time.perf_counter()-started}

def plants():
    # Known JSON text includes escapes and spans several tiny chunks.
    obj={'records':[{'name':'known','body':'A\\B\n"quote"'+'x'*10000,'type':'Nat'},
                    {'name':'null','body':None,'type':'True'}]}
    source=HERE/'stream-positive.json';source.write_text(json.dumps(obj,indent=2)+'\n')
    record=dehydrate(source,HERE/'stream-positive-digest.json',chunk=128)
    got=json.loads((HERE/'stream-positive-digest.json').read_text())
    expected=json.loads(json.dumps(obj))
    for row in expected['records']:
        for k in ['body','type']:
            if row[k] is not None:
                token=json.dumps(row[k]).encode()
                row[k]='RAW_JSON_TOKEN_SHA256:'+hashlib.sha256(token).hexdigest()
    assert got==expected and record['digest_fields']==4
    bad=json.loads(json.dumps(obj));bad['records'][0]['body']='corrupted'
    (HERE/'stream-corruption.json').write_text(json.dumps(bad,indent=2)+'\n')
    dehydrate(HERE/'stream-corruption.json',HERE/'stream-corruption-digest.json',chunk=128)
    assert json.loads((HERE/'stream-corruption-digest.json').read_text())!=expected
    # Full-path clean twin from the own frozen toy record, independently decode
    # metadata and ensure every original stored/private/generated row remains.
    toy=HERE.parent/'toys/AuditProducerFull-stored.json'
    dehydrate(toy,HERE/'stream-toy-digest.json')
    a=json.loads(toy.read_text());b=json.loads((HERE/'stream-toy-digest.json').read_text())
    assert len(a['stored_occurrences'])==len(b['stored_occurrences'])==33
    assert [r['name'] for r in a['stored_occurrences']]==[r['name'] for r in b['stored_occurrences']]
    return {'positive_exact_token_hash':True,'corruption_caught':True,'toy_occurrences_preserved':33}

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['plants','pilot','full']);args=ap.parse_args()
    if args.mode=='plants':d=plants()
    elif args.mode=='pilot':d=dehydrate(HERE/'AuditPilot.json',HERE/'AuditPilot-digest.json')
    else:d=dehydrate(HERE/'AuditScientific.json',HERE/'AuditScientific-digest.json')
    (HERE/('stream-'+args.mode+'-receipt.json')).write_text(json.dumps(d,indent=2)+'\n')
    print(json.dumps(d))
