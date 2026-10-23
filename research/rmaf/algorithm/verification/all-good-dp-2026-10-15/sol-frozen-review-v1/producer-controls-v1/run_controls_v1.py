from pathlib import Path
from hashlib import sha256
import json, subprocess, os, time, argparse, copy

H = Path(__file__).resolve().parent
ROOT = H.parents[6]
LEAN = ROOT / '.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'

def h(p): return sha256(p.read_bytes()).hexdigest()
def parse(s):
    out = {'modules': [], 'producers': [], 'occurrences': []}
    for line in s.splitlines():
        for prefix, key in [('MODULES\t','modules'),('PRODUCER\t','producers'),('OCCURRENCE\t','occurrences')]:
            if line.startswith(prefix):
                x=json.loads(line[len(prefix):])
                if key=='modules': out[key]=x
                else: out[key].append(x)
    return out

def signature(x):
    return sorted([(r['producer'],r['occurrenceIndex'],json.dumps(r['stored'],sort_keys=True)) for r in x['occurrences']])

def check(x, wanted, expected_count):
    assert len(x['occurrences'])==expected_count
    assert sorted(r['producer'] for r in x['producers'])==sorted(wanted)
    identities=[(r['producer'],r['occurrenceIndex']) for r in x['occurrences']]
    assert len(identities)==len(set(identities))
    for p in x['producers']:
        rows=[r for r in x['occurrences'] if r['producer']==p['producer']]
        assert [r['stored']['name'] for r in rows]==p['constNames']
        assert Path(p['oleanPath']).resolve()==(H/(p['producer']+'.olean')).resolve()
    bad=[(r['producer'],r['stored']['name']) for r in x['occurrences'] if r['stored']['kind']=='axiom']
    assert not bad, ('direct-custom-axioms',bad)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--pilot',action='store_true');args=ap.parse_args()
    start=time.perf_counter();pins=json.loads((H/'CONTROL-MANIFEST-v1.json').read_text())
    for e in pins['files']: assert h(H/e['path'])==e['sha256'],('source-byte',e['path'])
    ex=json.loads((H/'EXPECTATIONS-v1.json').read_text());logs=H/'logs';logs.mkdir(exist_ok=True);procs=[]
    def run(label,cmd):
        t=time.perf_counter();r=subprocess.run([str(LEAN),*cmd],cwd=H,env={**os.environ,'LEAN_PATH':str(H)},text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
        (logs/(label+'.log')).write_text(r.stdout);procs.append({'label':label,'exit':r.returncode,'seconds':time.perf_counter()-t});assert r.returncode==0,(label,r.stdout);return r.stdout
    if args.pilot:
        for m in ex['pilotModules']: run('pilot-'+m,['-o',m+'.olean',m+'.lean'])
        out={'status':'PILOT-PASS','seconds':time.perf_counter()-start,'processes':procs,'candidateContact':False}
        (H/'pilot-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));return
    for m in ['ProducerB','ProducerHostile']:run('compile-'+m,['-o',m+'.olean',m+'.lean'])
    clean=parse(run('clean',['ProbeClean.lean']));again=parse(run('clean-repeated',['ProbeClean.lean']));hostile=parse(run('hostile',['ProbeHostile.lean']))
    check(clean,ex['cleanImports'],ex['cleanSelectedOccurrences']);check(again,ex['cleanImports'],4)
    assert signature(clean)==signature(again),'exact-byte-body-repeat'
    shared=[r for r in clean['occurrences'] if r['stored']['name']=='ProducerCollision.shared']
    assert len(shared)==2 and len(set(r['stored']['typeExpr'] for r in shared))==1 and len(set(r['stored']['valueExpr'] for r in shared))==1
    assert all(r['stored']['kind']=='theorem' and 'True' in r['stored']['typeExpr'] and 'True.intro' in r['stored']['valueExpr'] for r in shared)
    assert len(set(r['stored']['name'] for r in clean['occurrences']))==3
    hidden=[r for r in hostile['occurrences'] if r['producer']=='ProducerHostile' and r['stored']['name']=='ProducerCollision.shared']
    assert len(hostile['occurrences'])==4 and len(hidden)==1
    q=hidden[0];assert q['stored']['kind']=='axiom' and q['stored']['valueExpr'] is None and q['stored']['typeExpr']==shared[0]['stored']['typeExpr']
    assert q['resolved']['kind']=='theorem' and q['resolvedOrigin']=='ProducerA'
    assert any(r['producer']=='ProducerHostile' and r['stored']['name']==ex['hostileOwnCleanName'] for r in hostile['occurrences'])
    catches=[]
    try:check(hostile,ex['hostileImports'],4)
    except AssertionError as e:catches.append({'id':'coalesced-custom-axiom','reason':str(e)})
    else:raise AssertionError('hostile producer accepted')
    for mutation in ['missing-occurrence','duplicate-occurrence','altered-type-bytes','altered-body-bytes','wrong-producer-origin']:
        c=copy.deepcopy(clean)
        if mutation=='missing-occurrence':c['occurrences'].pop()
        elif mutation=='duplicate-occurrence':c['occurrences'].append(copy.deepcopy(c['occurrences'][0]))
        elif mutation=='altered-type-bytes':c['occurrences'][0]['stored']['typeExpr']+=' CORRUPT'
        elif mutation=='altered-body-bytes':c['occurrences'][0]['stored']['valueExpr']='CORRUPT'
        else:c['occurrences'][0]['producer']='WrongProducer'
        try:check(c,ex['cleanImports'],4);assert signature(c)==signature(clean),'exact-byte-body-occurrence-adapter'
        except AssertionError as e:catches.append({'id':mutation,'reason':str(e)})
        else:raise AssertionError(('corruption accepted',mutation))
    source=(H/'ProducerA.lean').read_bytes();assert sha256(source+b'\n').hexdigest()!=h(H/'ProducerA.lean');catches.append({'id':'literal-source-byte-drift','reason':'same exact source hash comparator rejects appended newline'})
    assert [r['id'] for r in catches]==ex['expectedCorruptions']
    out={'status':'PRODUCER-CONTROLS-PASS','seconds':time.perf_counter()-start,'processes':procs,'clean':clean,'hostile':hostile,'corruptionsCaught':catches,'candidateContact':False,'extraIndependentReplications':0}
    (H/'fixed-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'corruptionsCaught':len(catches),'cleanOccurrences':4,'hostileOccurrences':4,'seconds':out['seconds']}))

if __name__=='__main__':main()
