#!/usr/bin/env python3
"""One-shot packaging only. Does not execute any scientific evaluator or proof."""
import datetime
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile

ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
X0=ROOT/'research/rmaf/algorithm/pair_case/cheap_high/x0'
DEST=X0/'sol-handoff-v1'
ARCHIVE=X0/'sol-handoff-v1.tar.gz'
EXTERNAL_SEAL=X0/'sol-handoff-v1.ARCHIVE-SEAL.json'
NATIVE=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
TC=NATIVE.parent.parent
if DEST.exists() or ARCHIVE.exists() or EXTERNAL_SEAL.exists():
    raise SystemExit('Refusing to replace an existing sealed handoff')

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
    return h.hexdigest()

def info(p):
    return {'absolute_path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}

def write_json(p,obj): p.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')

DEST.mkdir()
(DEST/'payload').mkdir()
(DEST/'provenance').mkdir()
owned=[]
for p in X0.iterdir():
    if p.is_file() and p.name.startswith('sol-') and not p.name.startswith('sol-handoff-v1'):
        owned.append(p)
owned += [p for p in (X0/'sol-lean').rglob('*') if p.is_file()]
omitted=[]
for p in sorted(owned):
    rel=p.relative_to(X0)
    if p.suffix in ['.olean','.ilean','.pyc']:
        omitted.append({**info(p),'reason':'Compiled or cache file omitted; identity retained'})
        continue
    target=DEST/'payload'/rel
    target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(p,target)
    if sha(p)!=sha(target): raise SystemExit('Snapshot copy mismatch: '+str(rel))

source_paths=[
 ROOT/'research/rmaf/lean/RMAF.lean',
 ROOT/'research/rmaf/algorithm/universal233/core/CoreProgram.lean',
 ROOT/'research/rmaf/algorithm/pair_case/cheap_high/TARGET-v1.md',
 ROOT/'research/rmaf/algorithm/pair_case/TARGET-v1.md',
 ROOT/'research/rmaf/algorithm/TARGET.md',
 ROOT/'research/rmaf/algorithm/universal233/core/lean-toolchain',
]
source_records=[]
for p in source_paths:
    rel=p.relative_to(ROOT); target=DEST/'provenance'/'sources'/rel
    target.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(p,target)
    source_records.append({**info(p),'snapshot_path':str(target.relative_to(DEST))})

version=subprocess.run([str(NATIVE),'--version'],capture_output=True,text=True,check=True)
linkage=subprocess.run(['/usr/bin/otool','-L',str(NATIVE)],capture_output=True,text=True,check=True)
(DEST/'provenance/native-lean-version.txt').write_text(version.stdout+version.stderr)
(DEST/'provenance/native-lean-linkage.txt').write_text(linkage.stdout+linkage.stderr)
shared=[
 ROOT/'research/rmaf/algorithm/universal233/core/build/CoreGraph.olean',
 ROOT/'research/rmaf/algorithm/universal233/core/build/RMAF.olean',
]
current_sources=[
 ROOT/'research/rmaf/algorithm/universal233/core/CoreGraph.lean',
 ROOT/'research/rmaf/algorithm/universal233/core/build/RMAF.lean',
 ROOT/'research/rmaf/lean/RMAF.lean',
]
runtime=[NATIVE]+[TC/'lib/lean'/n for n in ['libInit_shared.dylib','libleanshared_2.dylib','libleanshared_1.dylib','libleanshared.dylib']]
provenance={
 'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'operation':'Packaging existing evidence only; no scientific evaluator, census, test battery or proof rerun',
 'source_records':source_records,
 'native_lean':{'version_output':version.stdout.strip(),'toolchain_directory':str(TC),'files':[info(p) for p in runtime],
                'system_linkage_identity':'/usr/lib/libSystem.B.dylib compatibility 1.0.0 current 1356.0.0 (otool output retained); system library not packaged or hashed'},
 'shared_imported_binaries':[info(p) for p in shared],
 'associated_current_source_identities':[info(p) for p in current_sources],
 'dependency_chain':['LiteralReplay.lean / LiteralScopeReplay.lean import Lean and CoreProgram',
                     'Freshly compiled unchanged CoreProgram.lean imports existing CoreGraph.olean',
                     'CoreGraph.lean import header is RMAF; existing RMAF.olean reused'],
 'boundary':'CoreGraph dependency was neither rebuilt nor reviewed. Recording its current source hash does not establish binary-to-source correspondence. Existing imported binaries were reused for finite program execution; these runs are not universal Lean proofs.',
 'fresh_compile_command':'LEAN_PATH='+str(ROOT/'research/rmaf/algorithm/universal233/core/build')+' '+str(NATIVE)+' -o '+str(X0/'sol-lean/CoreProgram.olean')+' '+str(ROOT/'research/rmaf/algorithm/universal233/core/CoreProgram.lean'),
 'replay_environment':{'LEAN_PATH':str(X0/'sol-lean')+':'+str(ROOT/'research/rmaf/algorithm/universal233/core/build'),'native_executable':str(NATIVE),'mode':'--run'},
 'omitted_binary_and_cache_files':omitted,
 'all_three_main_milestones':'OPEN',
}
write_json(DEST/'provenance/PROVENANCE.json',provenance)
(DEST/'README.txt').write_text(
 'Cheap/high independent X0 immutable handoff v1\n\n'
 'Finite NO-FIRE evidence. All three main milestones remain OPEN.\n'
 'This snapshot preserves the existing sources, frozen fixtures, controls, results, logs,\n'
 'and failed attempts. It adds packaging provenance only; no scientific results were rerun.\n'
 'Read payload/sol-REPORT-v1.md for exact scope and unresolved consumer obligations.\n'
 'CoreGraph was not rebuilt or reviewed. These are finite program executions, not universal Lean proofs.\n'
 'Bulky compiled binaries are omitted but their SHA256s and dependency identities are retained.\n'
 'Read-only permissions protect the snapshot against accidental writes; SHA256 seals detect changes.\n'
 'No WORM or trusted timestamp service is asserted.\n\n'
 'MANIFEST.json records every payload/provenance file SHA256.\n'
 'FILES.sha256 supplies a standard relative-path checksum list.\n'
 'SEAL.json identifies those two records. The external ARCHIVE-SEAL identifies the tar.gz.\n')

entries=[]
for p in sorted(DEST.rglob('*')):
    if p.is_file():
        entries.append({'path':p.relative_to(DEST).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)})
write_json(DEST/'MANIFEST.json',{
 'schema':'cheap-high-x0-handoff-manifest/v1','owner':'sol-cheap-high-x0',
 'entry_count':len(entries),'entries':entries,
 'ownership_selector':'Original x0 top-level sol-* files and sol-lean files; shared sources/provenance listed explicitly',
 'scientific_scope':'Finite program executions and exact finite graph/partition controls; no universal Lean proofs',
 'all_three_main_milestones':'OPEN',
})
(DEST/'FILES.sha256').write_text(''.join(x['sha256']+'  '+x['path']+'\n' for x in entries))
write_json(DEST/'SEAL.json',{
 'schema':'cheap-high-x0-handoff-seal/v1',
 'manifest_sha256':sha(DEST/'MANIFEST.json'),
 'checksum_list_sha256':sha(DEST/'FILES.sha256'),
 'payload_entry_count':len(entries),
 'all_three_main_milestones':'OPEN',
})

# Seal the unchanged snapshot before archiving. Archive metadata is normalized.
for p in DEST.rglob('*'):
    if p.is_file(): p.chmod(0o444)
for p in sorted((p for p in DEST.rglob('*') if p.is_dir()),reverse=True): p.chmod(0o555)
DEST.chmod(0o555)
with ARCHIVE.open('wb') as raw:
    with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as gz:
        with tarfile.open(fileobj=gz,mode='w',format=tarfile.PAX_FORMAT) as tf:
            for p in [DEST]+sorted(DEST.rglob('*')):
                ti=tf.gettarinfo(str(p),arcname=(Path(DEST.name)/p.relative_to(DEST)).as_posix())
                ti.uid=ti.gid=0; ti.uname=ti.gname=''; ti.mtime=0
                ti.pax_headers={}
                if p.is_file():
                    with p.open('rb') as f: tf.addfile(ti,f)
                else: tf.addfile(ti)
ARCHIVE.chmod(0o444)
seal={
 'schema':'cheap-high-x0-archive-seal/v1',
 'manifest':info(DEST/'MANIFEST.json'),
 'snapshot_seal':info(DEST/'SEAL.json'),
 'archive':info(ARCHIVE),
 'scientific_reruns':0,
 'all_three_main_milestones':'OPEN',
}
write_json(EXTERNAL_SEAL,seal); EXTERNAL_SEAL.chmod(0o444)
print(json.dumps(seal,indent=2,sort_keys=True))
