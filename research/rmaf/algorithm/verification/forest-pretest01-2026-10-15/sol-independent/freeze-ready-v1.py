#!/usr/bin/env python3
"""One-shot immutable READY inventory, only own files and licensed inputs."""
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import time

HERE=Path(__file__).resolve().parent
BASE=HERE.parent
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
def pin(path):
    b=path.read_bytes()
    return {'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}

started=time.perf_counter()
out=HERE/'READY-v1.json'
assert not out.exists(), 'refuse READY overwrite'
assert shutil.disk_usage(HERE).free>=3*2**30
inputs=[BASE/'TARGET-v1.md',BASE/'PUBLIC-DEFINITIONS-v1.json',
        BASE.parent/'both-bad-2026-10-15'/'PUBLIC-DEFINITIONS-v1.json',
        BASE/'ROOT-RUNTIME-LICENSE-v1.md',
        ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean',
        ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Lean/Expr.lean']
assert pin(inputs[1])['sha256']=='243a9b6e41cdbc2116f1adacd8d87ad38a19fc330078cab7d5f695c416b45565'
assert pin(inputs[2])['sha256']=='c413d7437ef472976dbdeffc432401fbed88ba1d71c51e7822022fcb776e29ac'
files=sorted(p for p in HERE.rglob('*') if p.is_file())
compressed_total=sum(len(gzip.compress(p.read_bytes(),mtime=0)) for p in files)
assert compressed_total<=256*2**20
ready={'status':'READY_QUALIFIED_AWAITING_EXACT_ROOT_RELEASE','utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
       'target':'full-current-forest cost0/1 named main-dispatcher pretest',
       'candidate_contact':False,'exact_root_release':False,
       'summary_exposure':'incidental team inventory after graph controls; before producer implementation; quarantined',
       'graph':{'pilot':'graph-pilot-v1.json','full':'graph-controls-v1.json','fixtures':27,'caught_corruptions':14},
       'producer':{'pilot':'producer-controls-pilot-v1.json','full':'producer-controls-v3.json','controls':19,'commands':11},
       'failed_receipts':['lean-api-pilot-v1.json','lean-api-pilot-v3.json','producer-compile-pilot-v1.json',
                          'producer-controls-v1.json','producer-controls-v2.json'],
       'contacts':'CONTACT-LINEAGE-v1.md','failure_ledger':'FAILURE-LEDGER-v1.md','plan':'READY-NOTES-v1.md',
       'scope_debts':'all global Algorithm/Correctness/Smaller-base/novelty/VERIFIED-CLOSED OPEN; candidate unread; runtime/IR not verified',
       'resource_caps':{'new_compressed_bytes':256*2**20,'minimum_free_bytes':3*2**30,'command_timeout_seconds':60},
       'measured_compressible_inventory_bytes':compressed_total,'disk_free_bytes':shutil.disk_usage(HERE).free,
       'licensed_inputs':[pin(p) for p in inputs],'own_artifacts':[pin(p) for p in files],
       'freeze_seconds':time.perf_counter()-started}
out.write_text(json.dumps(ready,indent=2)+'\n')
print(json.dumps({'ready':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),
                  'own_artifacts':len(files),'compressible_bytes':compressed_total,'free_bytes':ready['disk_free_bytes']}))
