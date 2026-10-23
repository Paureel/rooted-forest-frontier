"""One-shot fresh Case322 producer controls, using own pinned frozen auditor.
No candidate imports; no extra independent replication credit for shared layers.
"""
import argparse, copy, hashlib, importlib.util, json, os, pathlib, subprocess, time, traceback
H=pathlib.Path(__file__).resolve().parent
ROOT=next(p for p in H.parents if(p/'bootloops-python').exists())
OLD=ROOT/'research/rmaf/algorithm/verification/rule4-2026-10-15/sol-independent'
AUD=OLD/'ProducerAudit.lean';VALID=OLD/'producer_controls.py';C=H/'producer-controls'
PINS={'ProducerAudit.lean':'c88072d2de00a009df451c89546a918074e2dcb0e0376e0eec649b48fd843e7f',
      'producer_controls.py':'d49953e9ec58a16727caaecbe0fd4bbabe40fe6e89f759de273300ef8855f554'}
for name,sha in PINS.items():assert hashlib.sha256((OLD/name).read_bytes()).hexdigest()==sha
spec=importlib.util.spec_from_file_location('own_frozen_validator',VALID)
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
LEAN=ROOT/'bootloops-lean'
SOURCES={
'Case322CleanA':'import Std\nnamespace Case322Same\ntheorem token : True := True.intro\nend Case322Same\n',
'Case322CleanB':'import Std\nnamespace Case322Same\ntheorem token : True := True.intro\nend Case322Same\n',
'Case322Hostile':'import Std\nnamespace Case322Same\naxiom token : True\ntheorem ownClean : True := True.intro\nend Case322Same\n',
'Case322Unused':'import Std\naxiom Case322Unused.hidden : Nat\ntheorem Case322Unused.clean : True := True.intro\n',
'Case322Private':'import Std\nnamespace Case322Private\nprivate axiom hidden : Nat\nnoncomputable def generated : Nat → Nat\n | 0 => hidden\n | n+1 => generated n\ntheorem clean : True := True.intro\nend Case322Private\n',
'Case322False':'import Std\ntheorem Case322False.bad : (1:Nat)=2 := by decide\n',
'Case322Val1':'import Std\nnamespace Case322Value\ndef token : Nat := 1\nend Case322Value\n',
'Case322Val2':'import Std\nnamespace Case322Value\ndef token : Nat := 2\nend Case322Value\n',
'Case322Type':'import Std\nnamespace Case322Same\ntheorem token : (1:Nat)=1 := rfl\nend Case322Same\n',
'Case322Import':'import Init\nnamespace Case322Same\ntheorem token : True := True.intro\nend Case322Same\n',
}
def digest(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def run(argv,tag,expected=None):
    dest=H/(tag+'.json')
    if dest.exists():raise ValueError('preserve previous run')
    env=os.environ.copy();env['LEAN_PATH']=str(C);start=time.perf_counter()
    try:
        p=subprocess.run([str(x)for x in argv],cwd=C,env=env,capture_output=True,text=True,timeout=30)
        r=dict(argv=[str(x)for x in argv],cwd=str(C),LEAN_PATH=str(C),returncode=p.returncode,
               seconds=time.perf_counter()-start,stdout=p.stdout,stderr=p.stderr)
        if len(p.stdout)+len(p.stderr)>4000000:raise ValueError('control output cap4MB')
        dest.write_text(json.dumps(r,indent=2)+'\n')
        if expected is not None and p.returncode!=expected:raise AssertionError((tag,p.returncode,expected))
        return r
    except Exception:
        with(H/'producer-failures-v1.log').open('a')as f:f.write(traceback.format_exc()+'\n')
        raise
def pin():return {str(p):digest(p)for p in sorted(C.glob('*.lean'))+[AUD,VALID,H/'producer_controls.py']}
def check(name,ok,checks):
    checks.append(dict(name=name,passed=bool(ok)))
    if not ok:raise AssertionError(name)
def audit(names,tag,expect=0):
    r=run([LEAN,'--run',AUD,*names],tag,expect);record=json.loads(r['stdout'])
    (H/(tag+'-record.json')).write_text(json.dumps(record,indent=2)+'\n')
    return record
def rows(record,name):return [r for r in record['occurrences']if r['name']==name]
def setup():
    C.mkdir(exist_ok=True)
    for name,text in SOURCES.items():
        p=C/(name+'.lean')
        if p.exists():assert p.read_text()==text
        else:p.write_text(text)
    (H/'producer-source-pins-v1.json').write_text(json.dumps(pin(),indent=2)+'\n')
def main():
    p=argparse.ArgumentParser();p.add_argument('--mode',choices=['setup','pilot','battery'],required=True);a=p.parse_args()
    if a.mode=='setup':setup();return
    pins=pin();checks=[];start=time.perf_counter()
    if a.mode=='pilot':
        run([LEAN,'-o',C/'Case322CleanA.olean',C/'Case322CleanA.lean'],'producer-pilot-compile',0)
        clean=audit(['Case322CleanA'],'producer-pilot-audit')
        check('fresh clean producer actual theorem',v.validate(clean,pins)and len(rows(clean,'Case322Same.token'))==1 and rows(clean,'Case322Same.token')[0]['kind']=='theorem',checks)
    else:
        for name in SOURCES:
            if name=='Case322CleanA':continue
            run([LEAN,'-o',C/(name+'.olean'),C/(name+'.lean')],'producer-compile-'+name,1 if name=='Case322False'else 0)
        for ns,tag in [(['Case322CleanA','Case322CleanB'],'clean-AB'),(['Case322CleanB','Case322CleanA'],'clean-BA')]:
            clean=audit(ns,'producer-'+tag)
            check(tag+' actual both stored theorem producers',v.validate(clean,pins)and len(rows(clean,'Case322Same.token'))==2,checks)
        for ns,tag in [(['Case322CleanA','Case322Hostile'],'hostile-AH'),(['Case322Hostile','Case322CleanA'],'hostile-HA'),(['Case322Unused'],'unused'),(['Case322Private'],'private-generated')]:
            bad=audit(ns,'producer-'+tag,2)
            check(tag+' direct axiom rejected',v.catches(lambda:v.validate(bad,pins)),checks)
            if 'hostile'in tag:
                check(tag+' stored hostile+clean visible',any(r['producer']=='Case322Hostile'and r['kind']=='axiom'for r in bad['occurrences'])and any(r['name']=='Case322Same.ownClean'for r in bad['occurrences']),checks)
            if tag=='private-generated':
                check('private generated dependency visible',any('generated'in r['name']and any('hidden'in ax for ax in r['axioms'])for r in bad['occurrences']),checks)
        clean=audit(['Case322CleanA'],'producer-clean-single')
        for tag,change in [
            ('missing',lambda r:r['occurrences'].pop()),('duplicate',lambda r:r['occurrences'].append(copy.deepcopy(r['occurrences'][0]))),
            ('index',lambda r:r['occurrences'][0].update(index=900)),('path-origin',lambda r:r['occurrences'][0].update(resolved_producer='WrongPath')),
            ('kind',lambda r:r['occurrences'][0].update(kind='axiom')),('type',lambda r:r['occurrences'][0].update(type='corrupt')),
            ('body',lambda r:r['occurrences'][0].update(body='corrupt')),('reference',lambda r:r['occurrences'][0].update(references=['bad'])),
            ('import',lambda r:r['occurrences'][0].update(imports=['BadImport']))]:
            bad=copy.deepcopy(clean);change(bad)
            check('exact '+tag+' corruption caught',v.catches(lambda:v.validate(bad,pins))or v.catches(lambda:v.frozen_equal(bad,clean)),checks)
            check('clean twin '+tag,v.validate(clean,pins)and v.frozen_equal(clean,clean)is None,checks)
        for name in ['Case322Type','Case322Import']:
            record=audit([name],'producer-'+name)
            # Compare payload and imports by same declaration name, not producer text alone.
            r=rows(record,'Case322Same.token')[0];rr=rows(clean,'Case322Same.token')[0]
            key='type'if name=='Case322Type'else'imports'
            check('actual compiled '+key+' differs',r[key]!=rr[key],checks)
        one=audit(['Case322Val1'],'producer-value1');two=audit(['Case322Val2'],'producer-value2')
        r1,r2=rows(one,'Case322Value.token')[0],rows(two,'Case322Value.token')[0]
        check('actual nonproof same type different body retained',r1['kind']==r2['kind']=='definition'and r1['type']==r2['type']and r1['body']!=r2['body'],checks)
        # Source/path pins protect the producing bytes independently of theorem payloads.
        changed=copy.deepcopy(pins);changed[str(C/'Case322CleanA.lean')]='0'*64
        check('exact source corruption caught',v.catches(lambda:v.validate(clean,changed)),checks)
        wrongpath=copy.deepcopy(pins);wrongpath[str(C/'missing-path.lean')]=wrongpath.pop(str(C/'Case322CleanA.lean'))
        try:v.validate(clean,wrongpath)
        except FileNotFoundError:caught=True
        else:caught=False
        check('missing actual path caught',caught,checks)
        for ns,tag in [(['Case322Val1','Case322Val2'],'values12'),(['Case322Val2','Case322Val1'],'values21')]:
            result=run([LEAN,'--run',AUD,*ns],'producer-'+tag)
            if result['returncode']==0:
                record=json.loads(result['stdout']);actual=rows(record,'Case322Value.token')
                check(tag+' actual stored bodies retained',len(actual)==2 and {r['body']for r in actual}=={r1['body'],r2['body']},checks)
                check(tag+' no type-only interchangeability',v.catches(lambda:v.frozen_equal(actual[0]['body'],actual[1]['body'])),checks)
            else:
                check(tag+' import refuses incompatible values',bool(result['stderr']or result['stdout']),checks)
        sysroot=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0'
        artifacts=[sysroot/'bin/lean',sysroot/'lib/lean/Std.olean',sysroot/'lib/lean/Init.olean',sysroot/'lib/lean/Lean.olean']
        (H/'installed-trust-pilot-pins-v1.json').write_text(json.dumps({str(p):digest(p)for p in artifacts},indent=2)+'\n')
    out=dict(mode=a.mode,checks=checks,passed=len(checks),seconds=time.perf_counter()-start,source_pins=pins,
             scope='new Std-only controls; own frozen auditor/validator reused with zero replication credit; installed libraries trusted/pinned')
    (H/('producer-'+a.mode+'-results-v1.json')).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(mode=a.mode,passed=len(checks),seconds=out['seconds'])))
if __name__=='__main__':
    try:main()
    except Exception:
        with(H/'producer-failures-v1.log').open('a')as f:f.write(traceback.format_exc()+'\n')
        raise
