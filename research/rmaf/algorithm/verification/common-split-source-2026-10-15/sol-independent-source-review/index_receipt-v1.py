#!/usr/bin/env python3
"""Bounded sequential producer receipt index; actual bodies remain on disk.
Registry must be fixed before the audited compile. Controls exercise this here;
no candidate registry or candidate path is accepted before exact root RELEASE.
"""
import argparse,hashlib,importlib.util,json,pathlib,sqlite3,time
P=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('own_dag',P/'check_controls.py');dag=importlib.util.module_from_spec(spec);spec.loader.exec_module(dag)
CAP=32*1024*1024

def h(x):return hashlib.sha256(dag.canonical(x)).hexdigest()
def bytehash(q):
    z=hashlib.sha256()
    with pathlib.Path(q).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):z.update(block)
    return z.hexdigest()
def typehash(s):
    hs=[]
    for node in s['nodes']:
        a=list(node)
        for pos in dag.CHILDREN[a[0]]:a[pos]=hs[a[pos]]
        hs.append(h(a))
    return hs[s['type_root']]
def signature(s):return h([s['name'],s['levels'],typehash(s)])
def closure_issues(cl):
    out=[]
    for k in ('missing','unsafe','partial'):
        if cl[k]:out.append(k+':'+str(cl[k]))
    if set(cl['axioms'])-dag.ALLOWED:out.append('disallowed_axioms:'+str(cl['axioms']))
    return out

def index(receipt,registry_file,database):
    start=time.perf_counter();reg=json.loads(pathlib.Path(registry_file).read_text());mapping=reg['scientific_modules'];std=reg['trusted_olean_pins'];trusted_root=pathlib.Path(reg['trusted_library_root']).resolve()
    # Hash/source checks occur before parsing any proof payload.
    for module,v in mapping.items():
        if bytehash(v['source'])!=v['source_sha256']:raise ValueError('source bytes differ from fixed registry: '+module)
        if bytehash(v['olean'])!=v['olean_sha256']:raise ValueError('olean bytes differ from fixed registry: '+module)
    if pathlib.Path(database).exists():raise ValueError('database exists; retain original attempt')
    db=sqlite3.connect(database)
    db.executescript('CREATE TABLE modules(name TEXT PRIMARY KEY, path TEXT); CREATE TABLE parts(producer TEXT, part INT, n INT, path TEXT, is_module INT, imports_hash TEXT, PRIMARY KEY(producer,part)); CREATE TABLE occurrences(producer TEXT, part INT, idx INT, name TEXT, kind TEXT, stored_hash TEXT, signature TEXT, body_present INT, resolved_hash TEXT, origin TEXT, issue_json TEXT, view_json TEXT, PRIMARY KEY(producer,part,idx));')
    rows=0;maxrow=0;extra=0;views=0
    with pathlib.Path(receipt).open('rb') as f:
        while True:
            line=f.readline(CAP+1)
            if not line:break
            if len(line)>CAP:raise ValueError('32-MiB row cap exceeded; no scope acceptance')
            maxrow=max(maxrow,len(line));r=json.loads(line);tag=r['record']
            if tag=='module':
                module=r['module'];path=pathlib.Path(r['olean_parts'][0]).resolve()
                if module in mapping:
                    if path!=pathlib.Path(mapping[module]['olean']).resolve():raise ValueError('logical module/olean mapping mismatch')
                elif not path.is_relative_to(trusted_root):raise ValueError('unexpected imported module origin')
                for raw in r['olean_parts']:
                    q=pathlib.Path(raw).resolve()
                    if module not in mapping and (str(q) not in std or bytehash(q)!=std[str(q)]):raise ValueError('unregistered/altered standard-library part')
                db.execute('INSERT INTO modules VALUES (?,?)',(module,str(path)))
            elif tag=='producer_part':
                p=r['producer'];part=r['part']
                if p not in mapping:raise ValueError('unmapped scientific producer')
                expected=pathlib.Path(mapping[p]['olean']).resolve()
                q=pathlib.Path(r['path']).resolve()
                if str(q) not in {str(expected),str(expected)+'.server',str(expected)+'.private'}:raise ValueError('scientific part path mismatch')
                if r.get('import_records') is None:raise ValueError('complete import flags missing')
                if [i['module_text'] for i in r['import_records']]!=r['imports']:raise ValueError('import order/name/flag representation mismatch')
                db.execute('INSERT INTO parts VALUES (?,?,?,?,?,?)',(p,part,r['occurrences'],str(q),r['is_module'],h(r['import_records'])))
                extra+=len(r['compiler_extra_names'])
            elif tag=='occurrence':
                s=r['stored'];dag.validate_dag(s['nodes'],[s['type_root'],s['body_root']]+[a[2] for a in s['rule_roots']]);issues=[];proof=r.get('exported_view_proof');view=None;effective=s;cl=r['closure']
                if proof is not None:
                    w=proof['stored'];dag.validate_dag(w['nodes'],[w['type_root'],w['body_root']]+[a[2] for a in w['rule_roots']])
                    view={'producer':proof['producer'],'part':proof['part'],'index':proof['index'],'stored_hash':h(w),'signature':signature(w),'closure_hash':h(proof['closure'])}
                    if not (s['kind']=='axiom' and not s['unsafe'] and proof['producer']==r['producer'] and w['kind']=='theorem' and w['body_root'] is not None and not w['unsafe'] and signature(s)==signature(w) and w['details']['all']==[s['name']]):issues.append('unqualified_same_producer_view')
                    effective=w;cl=proof['closure'];views+=1
                if effective['kind']=='axiom':issues.append('direct_custom_axiom')
                if effective['unsafe'] or effective['partial']:issues.append('unsafe_or_partial')
                issues.extend(closure_issues(cl))
                if r['resolved'] is None or h(effective)!=h(r['resolved']):issues.append('stored_resolved_body_kind_type_mismatch')
                # Compact view facts include a closure hash, not its body payload.
                if view:view['actual_closure_hash_required']=h(cl)
                row=(r['producer'],r['part'],r['index'],r['stored_name'],s['kind'],h(s),signature(s),s['body_root'] is not None,h(r['resolved']),r['resolved_origin'],json.dumps({'issues':issues,'closure_hash':h(r['closure'])}),json.dumps(view) if view else None)
                db.execute('INSERT INTO occurrences VALUES (?,?,?,?,?,?,?,?,?,?,?,?)',row);rows+=1
            elif tag!='encoder_controls':raise ValueError('unknown receipt record')
    db.commit();issues=[]
    for p,part,n,path,is_mod,ih in db.execute('SELECT * FROM parts'):
        got=db.execute('SELECT COUNT(*), MIN(idx), MAX(idx) FROM occurrences WHERE producer=? AND part=?',(p,part)).fetchone()
        if got[0]!=n or (n and (got[1]!=0 or got[2]!=n-1)):raise ValueError('missing/duplicate occurrence denominator')
    for p,part,idx,name,kind,sh,sig,body,resolved,origin,ij,vj in db.execute('SELECT * FROM occurrences'):
        partrow=db.execute('SELECT n,path,is_module FROM parts WHERE producer=? AND part=?',(p,part)).fetchone()
        if partrow is None or not 0<=idx<partrow[0]:raise ValueError('occurrence part attribution invalid')
        if db.execute('SELECT 1 FROM modules WHERE name=?',(origin,)).fetchone() is None:issues.append([p,part,idx,'resolved_origin_missing'])
        info=json.loads(ij)
        for message in info['issues']:issues.append([p,part,idx,message])
        if vj:
            v=json.loads(vj);last=db.execute('SELECT MAX(part) FROM parts WHERE producer=?',(p,)).fetchone()[0]
            wp=db.execute('SELECT path FROM parts WHERE producer=? AND part=?',(p,last)).fetchone()
            actual=db.execute('SELECT stored_hash,signature,issue_json FROM occurrences WHERE producer=? AND part=? AND idx=?',(v['producer'],v['part'],v['index'])).fetchone()
            if not (partrow[2] and v['producer']==p and part<last==v['part'] and wp[0].endswith('.olean.private') and actual and actual[0]==v['stored_hash'] and actual[1]==v['signature'] and json.loads(actual[2])['closure_hash']==v['closure_hash']):raise ValueError('private view proof missing/changed/wrong producer')
    db.close()
    return {'status':'REJECT' if issues else 'CLEAN_WITHIN_REPRESENTATION_SCOPE','stored_occurrences':rows,'qualified_view_records':views,'compiler_extra_names_uninspected':extra,'max_record_bytes':maxrow,'cap_bytes':CAP,'issues':issues,'seconds':time.perf_counter()-start,'registry_sha256':bytehash(registry_file),'receipt_sha256':bytehash(receipt),'scope':'compact SQLite index; per-occurrence lossless payload stays in receipt; not theorem acceptance'}

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('receipt');a.add_argument('registry');a.add_argument('database');args=a.parse_args();print(json.dumps(index(args.receipt,args.registry,args.database),sort_keys=True))
