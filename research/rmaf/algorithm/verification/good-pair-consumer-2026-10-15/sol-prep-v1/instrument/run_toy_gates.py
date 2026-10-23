#!/usr/bin/env python3
"""One-shot prerelease Lean/Std-only toy audit. No candidate module imports."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
P=Path(__file__).resolve().parent.parent
SRC=P/'toy-src'; BUILD=P/'toy-build';LOG=P/'logs'
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
POLICY=json.loads((P/'gate-policy-v1.json').read_text());ALLOW=set(POLICY['standard_axiom_allowlist'])
MODULES=['ToyClean','ToyUnusedAxiom','ToyPrivateAxiom','ToyExternal','ToyUseExternal','ToyRestriction','ToyExchangeRestriction','ToyRestrictionSource','ToyExchangeAdapted','ToyExchangeTampered','ToyCoverage','ToyExistingCoverage','ToyCoverageSource','ToyCoverageAdapted','ToyCoverageTampered']

def allowed_source(source):
    imports=re.findall(r'^import\s+(\S+)\s*$',source,re.M)
    return bool(imports) and all(m in set(MODULES)|{'AuditSupport','Lean','Std'} for m in imports)

def compile_one(name,stage,origin=None):
    path=SRC/(name+'.lean');text=path.read_text()
    if not allowed_source(text):raise RuntimeError('Unapproved import in isolated toy source '+name)
    env=os.environ.copy();env['LEAN_PATH']=str(BUILD)
    cmd=[str(LEAN),'-o',str(BUILD/(name+'.olean')),name+'.lean']
    start=time.perf_counter();run=subprocess.run(cmd,cwd=SRC,env=env,text=True,capture_output=True);seconds=time.perf_counter()-start
    log=LOG/(stage+'-'+name+'.log');log.write_text(run.stdout+run.stderr)
    meta={'module':name,'command':cmd,'cwd':str(SRC),'LEAN_PATH':str(BUILD),'seconds':seconds,'exit_code':run.returncode,'log':str(log.relative_to(P)),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
    if run.returncode:
        (LOG/(stage+'-'+name+'-failure.json')).write_text(json.dumps(meta,indent=2)+'\n');raise RuntimeError('Toy compilation failed: '+name)
    records=[json.loads(z[len('AUDIT_JSON '):]) for z in run.stdout.splitlines() if z.startswith('AUDIT_JSON ')]
    if origin is not None:
        if len(records)!=1 or records[0]['requested_origin']!=origin or not records[0]['count']:
            raise RuntimeError('Missing/nonunique/zero originating inventory '+name)
        meta['audit']=records[0]
    return meta

def observer_for(mod,stage):
    name='Origin'+mod
    (SRC/(name+'.lean')).write_text('import AuditSupport\nimport '+mod+'\naudit_import "'+mod+'"\n')
    return compile_one(name,stage,mod)

def evaluate_inventory(audit):
    ds=audit['declarations'];bad=[]
    for d in ds:
        extra=[a for a in d['axioms'] if a not in ALLOW]
        if d['kind']=='axiom' and d['name'] not in ALLOW:extra.append(d['name'])
        if extra:bad.append({'name':d['name'],'extra_axioms':sorted(set(extra))})
    return {'accept':bool(ds) and not bad,'originating_declarations':len(ds),'bad':bad}

def expected_adapter(original):
    if original=='ToyRestrictionSource':
        s=(SRC/'bodies/ToyRestrictionSource.lean').read_text()
        return s.replace('import ToyRestriction\n','import ToyExchangeRestriction\n').replace('ToyRestriction.Restriction','ToyExchangeRestriction.ExchangeRestriction')
    s=(SRC/'bodies/ToyCoverageSource.lean').read_text()
    return s.replace('import ToyCoverage\n','import ToyExistingCoverage\n').replace('ToyCoverage.flag','ToyExistingCoverage.flag')

def verdicts(rows):
    checks=[]
    def add(name,got,want=True):checks.append({'name':name,'got':got,'expected':want,'pass':got==want})
    originmap={r['module']:r['audit'] for r in rows if not r['module'].startswith('Origin') and 'audit'in r}
    imported={r['audit']['requested_origin']:r['audit'] for r in rows if r['module'].startswith('Origin') and 'audit'in r}
    inventories={m:evaluate_inventory(a) for m,a in originmap.items()}
    for m in MODULES:
        clean=m not in ['ToyUnusedAxiom','ToyPrivateAxiom','ToyExternal','ToyUseExternal']
        add(m+' full-origin axiom verdict',inventories[m]['accept'],clean)
        add(m+' source/import full inventory match',originmap[m]['declarations']==imported[m]['declarations'])
        add(m+' every declaration correct origin',all(d['origin']==m for d in originmap[m]['declarations']))
    clean=originmap['ToyClean']['declarations']
    add('private clean declaration inventoried',any(d['private'] and d['user_name']=='ToyClean.hidden' for d in clean))
    add('generated recursor inventoried',any(d['name']=='ToyClean.Packet.rec' and d['kind']=='recursor' for d in clean))
    unused=originmap['ToyUnusedAxiom']['declarations']
    add('unused outside-namespace custom axiom inventoried',any(d['name']=='outside_namespace_unused' and d['kind']=='axiom' for d in unused))
    add('unused-axiom public theorem closure clean',next(d for d in unused if d['name']=='ToyUnusedAxiom.harmless')['axioms'],[])
    prefix={'declarations':[d for d in unused if d['name'].startswith('ToyUnusedAxiom.') ]}
    add('namespace-only axiom audit false acceptance demonstrated',evaluate_inventory(prefix)['accept'])
    priv=originmap['ToyPrivateAxiom']['declarations']
    add('private custom axiom inventoried',any(d['private'] and d['kind']=='axiom' for d in priv))
    ext=originmap['ToyUseExternal']['declarations']
    add('external axiom reached through closure',any('ToyExternal.importedBad' in d['axioms'] for d in ext))
    add('external consumer has no originating axiom',any(d['kind']=='axiom' for d in ext),False)
    add('zero originating denominator rejected',evaluate_inventory({'declarations':[]})['accept'],False)
    for old,good,bad in [('ToyRestrictionSource','ToyExchangeAdapted','ToyExchangeTampered'),('ToyCoverageSource','ToyCoverageAdapted','ToyCoverageTampered')]:
        expected=expected_adapter(old)
        add(good+' exact allowed source adapter',(SRC/'bodies'/f'{good}.lean').read_text()==expected)
        add(bad+' changed body rejected',(SRC/'bodies'/f'{bad}.lean').read_text()==expected,False)
        norm=lambda mod:sorted((d['user_name'],d['private'],d['kind']) for d in originmap[mod]['declarations'])
        add(good+' full private/generated origin mapping',norm(old)==norm(good))
    base=(SRC/'bodies/ToyClean.lean').read_text()
    add('isolated source clean imports',allowed_source(base))
    add('unapproved import rejected before compilation',allowed_source('import RMAF\n'+base),False)
    return checks,inventories

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('stage',choices=['pilot','battery']);a=ap.parse_args();start=time.perf_counter();rows=[]
    try:
        if a.stage=='pilot':
            rows.append(compile_one('AuditSupport','pilot'))
            rows.append(compile_one('ToyClean','pilot','ToyClean'));rows.append(observer_for('ToyClean','pilot'))
            inv=evaluate_inventory(rows[1]['audit']);ok=inv['accept'] and rows[1]['audit']['declarations']==rows[2]['audit']['declarations']
            out={'phase':'PRE-CANDIDATE ONLY','stage':'pilot','executions':rows,'clean_accepts':inv,'source_import_equal':rows[1]['audit']['declarations']==rows[2]['audit']['declarations'],'all_pass':ok}
        else:
            pilot=json.loads((P/'toy-pilot-v1.json').read_text());rows+=pilot['executions']
            if not pilot['all_pass']:raise RuntimeError('Pilot prerequisite failed')
            for m in MODULES[1:]:rows.append(compile_one(m,'battery',m));rows.append(observer_for(m,'battery'))
            checks,inv=verdicts(rows)
            out={'phase':'PRE-CANDIDATE ONLY','stage':'battery','executions':rows,'checks':checks,'inventories':inv,'check_denominator':len(checks),'passed':sum(z['pass'] for z in checks),'all_pass':all(z['pass'] for z in checks)}
        out['seconds']=time.perf_counter()-start;out['candidate_compilation']=False;out['replication_increment']=0
        (P/('toy-'+a.stage+'-v1.json')).write_text(json.dumps(out,indent=2)+'\n')
        print(json.dumps({k:v for k,v in out.items() if k not in ['executions','checks','inventories']},indent=2))
        raise SystemExit(0 if out['all_pass'] else 1)
    except Exception as exc:
        failure={'phase':'PRE-CANDIDATE ONLY','stage':a.stage,'failure':repr(exc),'completed_executions':rows,'seconds':time.perf_counter()-start,'candidate_compilation':False}
        (P/('toy-'+a.stage+'-v1-FAILURE.json')).write_text(json.dumps(failure,indent=2)+'\n');raise
