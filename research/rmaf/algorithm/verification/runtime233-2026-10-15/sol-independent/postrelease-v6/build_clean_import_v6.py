from pathlib import Path
import datetime,gzip,hashlib,json,os,re,selectors,shutil,signal,subprocess,time
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=json.loads((HERE/'CLEAN-IMPORT-PLAN-v6.json').read_text())
assert (HERE/'BASELINE-CONTROL-RECEIPT-v6.json').exists()
lean=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
out=HERE/'clean-import-runs'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ');out.mkdir(parents=True)
shutil.copyfile(__file__,out/'runner.source.py');shutil.copyfile(HERE/'CLEAN-IMPORT-PLAN-v6.json',out/'plan.source.json')
def run(command,cwd,env,name):
    if shutil.disk_usage(HERE).free<plan['disk_floor_bytes']:raise RuntimeError('diskfloor')
    start=time.monotonic();deadline=start+plan['initial_subprocess_seconds']
    proc=subprocess.Popen(command,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
    select=selectors.DefaultSelector();select.register(proc.stdout,selectors.EVENT_READ)
    count=0;currentline=0;overflow=False;timeout=False;chunks=[]
    log=out/(name+'.log.gz')
    with gzip.open(log,'wb') as f:
        while select.get_map():
            if time.monotonic()>=deadline:timeout=True;os.killpg(proc.pid,signal.SIGKILL);break
            for key,_ in select.select(timeout=0.2):
                chunk=os.read(key.fd,8192)
                if not chunk:select.unregister(key.fileobj);continue
                count+=len(chunk)
                for line in chunk.splitlines(keepends=True):
                    currentline+=len(line)
                    if currentline>plan['line_cap_bytes']:overflow=True
                    if line.endswith(b'\n'):currentline=0
                if count>plan['raw_cap_bytes']:overflow=True
                if overflow:os.killpg(proc.pid,signal.SIGKILL);break
                f.write(chunk);chunks.append(chunk)
            if overflow:break
    proc.wait(timeout=2);select.close();proc.stdout.close()
    receipt={'command':command,'cwd':str(cwd),'LEAN_PATH':env['LEAN_PATH'],'seconds':time.monotonic()-start,'exit_code':proc.returncode,'timeout':timeout,'overflow':overflow,'raw_bytes':count,'log':log.name,'log_sha256':sha(log)}
    (out/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    if proc.returncode or timeout or overflow:raise RuntimeError('kernel process failed '+name)
    return b''.join(chunks).decode(),receipt

try:
 own=HERE/plan['source'];assert sha(own)==plan['source_sha256'];original=ROOT/plan['original_source'];assert sha(original)==plan['original_sha256'];assert own.read_text().splitlines()[1:]==original.read_text().splitlines()[1:]
 env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join([str(own.parent)]+[str(ROOT/r) for r in plan['roots']])
 _,compiled=run([str(lean),'-M3072','-o',str(own.with_suffix('.olean')),str(own)],own.parent,env,'clean-budget-compile')
 wrapper=out/'CleanBudgetCheck.lean';wrapper.write_text('import OWBudgets\n'+''.join('#check '+t+'\n#print axioms '+t+'\n' for t in plan['theorems']))
 printed,checked=run([str(lean),'-M3072',str(wrapper)],out,env,'clean-budget-interface')
 reports=re.findall(r"'[^']+' (?:does not depend on any axioms|depends on axioms: \[[^]]*\])",printed)
 axioms={x.strip() for b in re.findall(r'depends on axioms: \[([^]]*)\]',printed) for x in b.split(',') if x.strip()}
 assert len(reports)==2 and axioms<={'propext','Classical.choice','Quot.sound'}
 own.with_suffix('.olean').chmod(0o444);own.parent.chmod(0o555)
 receipt={'status':'OWN_IMPORT_ONLY_ADAPTATION_RECHECKED','original_source':plan['original_source'],'original_sha256':plan['original_sha256'],'only_change':plan['only_change'],'own_import_pins':{str(f.relative_to(HERE)):sha(f) for f in [own,own.with_suffix('.olean')]},'theorems':plan['theorems'],'axiom_reports':reports,'axioms':sorted(axioms),'compile':compiled,'interface':checked,'logs_relative_directory':str(out.relative_to(HERE)),'author_controls_imported_or_executed':False,'canonical_C_dependency_replay':False,'new_blind_replication_credit':0}
 (HERE/'CLEAN-IMPORT-RECEIPT-v6.json').write_text(json.dumps(receipt,indent=2)+'\n');(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt['status']);print('Two exact theorem bodies; one import change; standard axioms.');print(str(out))
except BaseException as e:
 (out/'failure.json').write_text(json.dumps({'error':repr(e)},indent=2)+'\n');raise
