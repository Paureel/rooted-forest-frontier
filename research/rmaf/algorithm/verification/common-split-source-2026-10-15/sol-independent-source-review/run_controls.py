#!/usr/bin/env python3
"""Fresh one-shot prerelease source-audit control runner; no candidate reads."""
import argparse,hashlib,json,os,pathlib,subprocess,time
P=pathlib.Path(__file__).resolve().parent
ROOT=P.parents[5]
SYSROOT=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0'
LEAN=SYSROOT/'bin/lean'
ENV=os.environ.copy();ENV.update(LEAN_PATH=str(P/'controls'),AUDIT_SYSROOT=str(SYSROOT))

def run(label,cmd,cwd=P,expected_code=0,timeout=30):
    path=P/f'{label}.log'
    if path.exists():raise RuntimeError('preserve existing attempt '+label)
    start=time.perf_counter()
    try:
        result=subprocess.run([str(c) for c in cmd],cwd=cwd,env=ENV,text=True,capture_output=True,timeout=timeout)
        code=result.returncode;output=result.stdout+result.stderr
    except subprocess.TimeoutExpired as exc:
        code=124;output=f'TIMEOUT after {timeout}s\n'+str(exc.stdout)+str(exc.stderr)
    duration=time.perf_counter()-start
    path.write_text(output)
    record={'label':label,'command':[str(c) for c in cmd],'cwd':str(cwd),'expected_code':expected_code,'actual_code':code,'seconds':duration,'log':path.name}
    with (P/'EXECUTIONS.jsonl').open('a') as f:f.write(json.dumps(record,sort_keys=True)+'\n')
    if expected_code=='nonzero':assert code not in (0,124),record
    else:assert code==expected_code,record
    print(json.dumps(record,sort_keys=True),flush=True)
    return record

def main():
    a=argparse.ArgumentParser();a.add_argument('stage',choices=['pilot','compile','dump']);a.add_argument('--version',default='v1');v=a.parse_args()
    if v.stage=='pilot':
        run('pilot-clean-'+v.version,[LEAN,'-o','TrueDiagnostic.olean','TrueDiagnostic.lean'],P/'controls')
        run('pilot-detector-'+v.version,[LEAN,'-o',P/'ProducerAudit.olean',P/'ProducerAudit.lean'])
    elif v.stage=='compile':
        for name in ('CleanBase','CleanTwin','CoalescedBad','AxiomBad','UnsafeBad','SorryBad'):
            run('compile-'+name+'-'+v.version,[LEAN,'-o',name+'.olean',name+'.lean'],P/'controls')
        run('compile-FalseDiagnostic-'+v.version,[LEAN,'FalseDiagnostic.lean'],P/'controls','nonzero')
    else:
        for label,mods in [('clean',['CleanBase','TrueDiagnostic']),('twins',['CleanBase','CleanTwin']),('coalesced',['CleanBase','CoalescedBad']),('axiom',['AxiomBad']),('unsafe',['UnsafeBad']),('sorry',['SorryBad'])]:
            run('dump-'+label+'-'+v.version,[LEAN,'--run',P/'ProducerAudit.lean',P/(label+'-'+v.version+'.jsonl'),*mods])
if __name__=='__main__':main()
