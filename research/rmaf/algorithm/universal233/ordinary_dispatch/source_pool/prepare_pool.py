"""Explicit author integration; one rebuilt directory, no binary-path mixing."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, time

R = Path(__file__).resolve().parents[6]
D = Path(__file__).resolve().parent
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
B = R/'results'/('algorithm-universal233-ordinary-source-pool-'+stamp)
B.mkdir()
sha = lambda b: hashlib.sha256(b).hexdigest()
inventory = json.loads((D/'INPUT-INVENTORY-v1.json').read_text())
controls = json.loads((D.parent/'producer_compatibility/COMPATIBILITY-CONTROLS-v1.json').read_text())
assert len(controls['checks']) == 3
for c in controls['checks']:
    assert bool(c['result']['rejects']) == c['expected_reject']
source = {}
for pack in inventory['packages']:
    for row in pack['sources']:
        p = R/row['source']
        data = p.read_bytes()
        assert sha(data) == row['sha256']
        source[(pack['package'],row['module'])] = (row,data.decode())

chosen, by_bytes, resolved, active = {}, {}, {}, set()
order = []
def resolve(key):
    if key in resolved:
        return resolved[key]
    assert key not in active, ('IMPORT_CYCLE',key)
    active.add(key)
    row, text = source[key]
    changes = {}
    lines = []
    for line in text.splitlines(keepends=True):
        if line.startswith('import '):
            match = re.fullmatch(r'import ([A-Za-z0-9_\'.]+)\s*',line)
            assert match, ('UNSUPPORTED_IMPORT_SYNTAX',key,line)
            dep = match[1]
            if (key[0],dep) in source:
                new = resolve((key[0],dep))
                if new != dep:
                    changes[dep] = new
                    line = 'import '+new+'\n'
            else:
                assert dep.split('.')[0] in {'Lean','Init','Std'}, ('UNPINNED_IMPORT',key,dep)
        lines.append(line)
    adapted = ''.join(lines).encode()
    ah = sha(adapted)
    if ah in by_bytes:
        name = by_bytes[ah]
        chosen[name]['origins'].append({'package':key[0],**row,'import_adaptations':changes})
    else:
        name = key[1]
        if name in chosen:
            name = 'Pool'+''.join(w.title() for w in key[0].split('_'))+name
        assert name not in chosen, ('MODULE_ALIAS_COLLISION',key,name)
        chosen[name] = {'module':name,'sha256':ah,'origins':[{'package':key[0],**row,'import_adaptations':changes}]}
        (B/(name+'.lean')).write_bytes(adapted)
        by_bytes[ah] = name
        order.append(name)
    active.remove(key)
    resolved[key] = name
    return name

for key in source:
    resolve(key)
(B/'lean-toolchain').write_bytes((R/'research/rmaf/lean/lean-toolchain').read_bytes())
mapping = [{'package':p,'original_module':n,'selected_module':v} for (p,n),v in resolved.items()]
rec = {'status':'SOURCE_POOL_CONSTRUCTION_RUNNING','all_three_main_milestones':'OPEN',
       'independent_acceptance':False,'full_algorithm':False,
       'runner_sha256':sha(Path(__file__).read_bytes()),
       'inventory_sha256':sha((D/'INPUT-INVENTORY-v1.json').read_bytes()),
       'compatibility_controls_sha256':sha((D.parent/'producer_compatibility/COMPATIBILITY-CONTROLS-v1.json').read_bytes()),
       'source_modules':[chosen[n] for n in order],'mapping':mapping,'runs':[]}
def save():
    (B/'construction.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
for name in order:
    p = B/(name+'.lean')
    assert sha(p.read_bytes()) == chosen[name]['sha256']
    start = time.monotonic()
    run = subprocess.run([str(R/'bootloops-lean'),'-o',str(B/(name+'.olean')),str(p)],
        cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),capture_output=True,text=True,timeout=60)
    log = run.stdout+run.stderr
    (B/(name+'.log')).write_text(log)
    rec['runs'].append({'module':name,'exit':run.returncode,'seconds':time.monotonic()-start,'log_sha256':sha(log.encode())})
    if run.returncode:
        rec['status']='SOURCE_POOL_CONSTRUCTION_STOPPED_AT_LITERAL_CONSUMER'
        rec['first_failed_module']=name
        save()
        print(json.dumps({'status':rec['status'],'directory':str(B),'module':name,'output':log}),flush=True)
        raise SystemExit(1)
    save()
rec['status']='SOURCE_POOL_ALL_LITERAL_SOURCES_REBUILT_PENDING_ORIGIN_AND_COMPATIBILITY_AUDIT'
save()
(D/'LATEST-CONSTRUCTION.json').write_text(json.dumps({'directory':str(B.relative_to(R)),'receipt_sha256':sha((B/'construction.json').read_bytes())},indent=2)+'\n')
print(json.dumps({'status':rec['status'],'directory':str(B),'source_modules':len(order),'original_entries':len(source)}),flush=True)
