#!/usr/bin/env python3
"""New caller-scoped controls of this agent's own producer instrument; no replication credit."""
import argparse,copy,hashlib,json,shutil,sys,time
from pathlib import Path
P=Path(__file__).resolve().parent; ROOT=P.parents[5]; O=P/'origin'
oldpath=ROOT/'research/rmaf/algorithm/verification/cherry-branch-2026-10-15/sol-main-necessity'
sys.path.insert(0,str(oldpath)); import origin_gate_v3 as old
PINS=json.loads((P/'ORIGIN-SOURCE-PINS-v1.json').read_text())
def pincheck():
    for f,h in PINS.items(): assert old.sha(P/f)==h,f
def enrich(d):
    for r in d['rows']:
        for k in ('type','body','recursor_rules','resolved_type','resolved_body','resolved_recursor_rules'):
            r[k+'_sha256']=hashlib.sha256(json.dumps(r[k],sort_keys=True).encode()).hexdigest() if k not in ('type','body') else None if r[k] is None else hashlib.sha256(r[k].encode()).hexdigest()
    return d
def fingerprint(d):
    return sorted((r['producer'],r['index'],r['name'],r['kind'],r['type_sha256'],r['body_sha256'],r['recursor_rules_sha256']) for r in d['rows'])
def gate(d,modules,imports=None,expected_fp=None):
    hs=d['producers']; loaded=set(d['loaded_modules'])
    if len(hs)!=len(modules) or {h['module'] for h in hs}!=set(modules): raise ValueError('producer header coverage')
    for h in hs:
        if type(h['count']) is not int or h['count']<0: raise ValueError('invalid stored count')
        if imports is not None and h['imports']!=imports[h['module']]: raise ValueError('actual stored import changed')
        if h['count']==0 and any(r['producer']==h['module'] for r in d['rows']): raise ValueError('fake empty producer')
    nonzero=[h['module'] for h in hs if h['count']>0]; reduced=dict(d); reduced['producers']=[h for h in hs if h['count']>0]
    old.gate(reduced,nonzero)
    for r in d['rows']:
        if r['resolved_origin'] not in loaded or r['resolved_type'] is None: raise ValueError('origin/unresolved constant')
        if 'Caller' in r['name']:
            owners={x['producer'] for x in d['rows'] if x['name']==r['name']}
            if r['resolved_origin'] not in owners: raise ValueError('fresh caller namespace origin corruption')
        if r['resolved_kind'] in ('definition','theorem','opaque') and r['resolved_body'] is None: raise ValueError('resolved body absent')
        for k in ('recursor_rules','resolved_type','resolved_body','resolved_recursor_rules'):
            if hashlib.sha256(json.dumps(r[k],sort_keys=True).encode()).hexdigest()!=r[k+'_sha256']: raise ValueError('actual '+k+' changed')
    if expected_fp is not None and fingerprint(d)!=expected_fp: raise ValueError('exact actual type/body adaptation')
    return True
def compile_one(n,src,build,label,records,expected=0): return old.compile_one(n,src,build,str(P/(label+'-v2')),records,expected)
def audit(ms,build,label,records):
    label += '-v2'
    r=old.run(['--run',str(O/'CallerProducerAudit_v2.lean')]+ms,O,build,str(P/label),records)
    if r.returncode: raise ValueError('auditor execution failure: '+label)
    d=enrich(json.loads(r.stdout)); (P/(label+'.json')).write_text(json.dumps(d,indent=2)+'\n'); return d
def reject(name,fn,results): return old.must_reject(name,fn,results)
def main():
    ap=argparse.ArgumentParser(); ap.add_argument('mode',choices=['pilot','full']); a=ap.parse_args(); records=[]; results=[]; started=time.perf_counter(); out=P/('origin-'+a.mode+'-v2-run1.json')
    report={'mode':a.mode,'commands':records,'controls':results,'candidate_contact':False,'replication_credit':0,'status':'FAIL','script_sha256':old.sha(Path(__file__)),'detector_sha256':old.sha(O/'CallerProducerAudit_v2.lean')}
    try:
        pincheck(); build=O/('build-'+a.mode+'-v2')
        names=['CallerCleanA','CallerCleanB'] if a.mode=='pilot' else ['CallerCleanA','CallerCleanB','CallerHostile','CallerUnused','CallerPrivate','CallerGenerated','CallerFalse','CallerEmpty']
        for n in names: compile_one(n,O,build,'origin-'+a.mode+'-compile-'+n,records,1 if n=='CallerFalse' else 0)
        cases=[(['CallerCleanA'],True),(['CallerCleanA','CallerCleanB'],True)]
        if a.mode=='full': cases += [(['CallerCleanB','CallerCleanA'],True),(['CallerGenerated'],True),(['CallerEmpty'],True),(['CallerUnused'],False),(['CallerPrivate'],False),(['CallerCleanA','CallerHostile'],False),(['CallerHostile','CallerCleanA'],False)]
        baseline=None
        for ms,clean in cases:
            tag='origin-'+a.mode+'-'+'+'.join(ms); d=audit(ms,build,tag,records); imports={m:['Init','Init','Std'] for m in ms}
            if clean: gate(d,ms,imports); results.append({'control':'+'.join(ms),'pass':True,'stored':len(d['rows'])})
            else: reject('+'.join(ms),lambda:gate(d,ms,imports),results)
            if ms==['CallerCleanA']: baseline=d
            shared=[r for r in d['rows'] if r['name']=='CallerDetector.shared']
            if len(ms)==2:
                assert len(shared)==2 and shared[0]['type']==shared[1]['type']
                if clean: assert len({r['body_sha256'] for r in shared})==2,'clean body difference must remain actual'
                else: assert {r['kind'] for r in shared}=={'axiom','theorem'} and all(r['resolved_kind']=='theorem' for r in shared)
                results.append({'control':'+'.join(ms)+' full occurrences','pass':True,'resolved_origins':[r['resolved_origin'] for r in shared],'body_hashes':[r['body_sha256'] for r in shared]})
            if ms==['CallerGenerated']:
                rr=next(r for r in d['rows'] if r['name']=='CallerGenerated.Token.rec'); assert len(rr['recursor_rules'])==2
                assert any(r['name'].startswith('_private.') for r in d['rows']); results.append({'control':'private/generated/recursor RHS','pass':True})
                corrupt=copy.deepcopy(d); next(r for r in corrupt['rows'] if r['name']=='CallerGenerated.Token.rec')['recursor_rules'][0]['rhs']+='CORRUPT'; reject('recursor RHS corruption',lambda:gate(corrupt,ms),results)
        if a.mode=='full':
            for tag,mut in [('missing occurrence',lambda d:d['rows'].pop()),('duplicate occurrence',lambda d:d['rows'].append(copy.deepcopy(d['rows'][0]))),('missing header',lambda d:d['producers'].clear()),('duplicate header',lambda d:d['producers'].append(copy.deepcopy(d['producers'][0]))),('fake empty producer',lambda d:d['producers'][0].update(count=0)),('wrong loaded origin',lambda d:d['rows'][0].update(resolved_origin='Std')),('unresolved reference',lambda d:d['rows'][0]['missing'].append('NotDefined')),('type receipt corruption',lambda d:d['rows'][0].update(type='CORRUPT')),('body receipt corruption',lambda d:d['rows'][0].update(body='CORRUPT')),('resolved body corruption',lambda d:d['rows'][0].update(resolved_body='CORRUPT'))]:
                d=copy.deepcopy(baseline); mut(d); reject(tag,lambda:gate(d,['CallerCleanA']),results)
            twin=O/'private-imports'; twin.mkdir(exist_ok=True)
            for producer,sub in [('CallerPrivateClean','private-clean'),('CallerPrivateHostile','private-hostile')]:
                src=O/sub; b=src/'build'; compile_one('SameCallerPrivate',src,b,'origin-'+producer+'-compile',records)
                for f in b.glob('SameCallerPrivate.*'): shutil.copyfile(f,twin/(producer+f.name[len('SameCallerPrivate'):]))
            clean=audit(['CallerPrivateClean'],twin,'origin-private-clean-twin',records); gate(clean,['CallerPrivateClean']); results.append({'control':'private coalesced clean twin','pass':True})
            for ms in [['CallerPrivateClean','CallerPrivateHostile'],['CallerPrivateHostile','CallerPrivateClean']]:
                d=audit(ms,twin,'origin-'+'+'.join(ms),records); rs=[r for r in d['rows'] if r['name'].startswith('_private.') and r['name'].endswith('.CallerPrivateTwin.shared')]; assert len(rs)==2 and rs[0]['name']==rs[1]['name'] and rs[0]['type']==rs[1]['type']; reject('private-unused-coalesced '+','.join(ms),lambda:gate(d,ms),results)
            adapt=O/'adaptations'; adapt.mkdir(exist_ok=True); source=(O/'CallerCleanA.lean').read_text()
            byte=adapt/'byte'; byte.mkdir(exist_ok=True); (byte/'CallerCleanA.lean').write_text(source+'\n')
            def byte_gate():
                if old.sha(byte/'CallerCleanA.lean')!=PINS['origin/CallerCleanA.lean']: raise ValueError('exact source byte changed')
            reject('exact source byte adaptation',byte_gate,results)
            for tag,text in [('type',source.replace('seed : Nat','seed : Int')),('body',source.replace(':= 7',':= 8')),('import',source.replace('import Std','import Lean'))]:
                src=adapt/tag; src.mkdir(exist_ok=True); (src/'CallerCleanA.lean').write_text(text); b=src/'build'; compile_one('CallerCleanA',src,b,'origin-adaptation-'+tag+'-compile',records); d=audit(['CallerCleanA'],b,'origin-adaptation-'+tag,records); reject('actual '+tag+' adaptation',lambda:gate(d,['CallerCleanA'],{'CallerCleanA':['Init','Init','Std']},fingerprint(baseline) if tag!='import' else None),results)
        pincheck(); report['status']='PILOT_PASS' if a.mode=='pilot' else 'CONTROLS_PASS'
    except Exception as ex: report['error']=repr(ex); raise
    finally:
        report['seconds']=time.perf_counter()-started; out.write_text(json.dumps(report,indent=2)+'\n'); print(json.dumps({'mode':a.mode,'status':report['status'],'controls':len(results),'seconds':report['seconds']}))
if __name__=='__main__': main()
