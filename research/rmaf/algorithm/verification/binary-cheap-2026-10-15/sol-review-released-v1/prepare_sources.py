#!/usr/bin/env python3
"""Exact released manifest/source identity and source-only isolated extraction."""
from pathlib import Path
import hashlib,json,re,shutil
P=Path(__file__).resolve().parent;ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
M=ROOT/'research/rmaf/algorithm/universal233/binary_cheap/BINARY-CHEAP-MANIFEST-v1.json';R=ROOT/'results/algorithm-universal233-binary-cheap-20261015T104014Z/certificate.json'
H='3936cb4b0a5d390972ad7b1fdace4166faa9a372cc9232329294a0f2b346d839'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads(M.read_text());r=json.loads(R.read_text());checks=[]
def add(n,v):checks.append({'name':n,'pass':bool(v)})
add('exact released manifest',h(M)==H);add('280 entries',len(m['immutable_files'])==280)
for e in m['immutable_files']:
 p=ROOT/e['path'];add(e['path'],p.is_file()and p.stat().st_size==e['bytes']and h(p)==e['sha256'])
for e in r['upstream_manifests']:add('upstream pin '+e['path'],h(ROOT/e['path'])==e['sha256'])
if not all(z['pass']for z in checks):raise SystemExit('Released manifest integrity failure')
S=P/'src';B=P/'build';L=P/'logs';O=P/'original-adapters'
for p in [S,B,L,O]:p.mkdir(exist_ok=True)
if list(B.iterdir()):raise SystemExit('Build directory not empty: refusing copied/stale scientific oleans')
rows=[]
for e in r['source_inputs']:
 original=ROOT/e['path'];canonical=R.parent/(e['module']+'.lean')
 add(e['module']+' exact producer source',h(original)==e['sha256']);add(e['module']+' exact compiled canonical source',h(canonical)==e['compiled_sha256'])
 source=canonical.read_text();imps=re.findall(r'^import\s+(\S+)\s*$',source,re.M)
 add(e['module']+' pinned imports only',all(x in r['positive_order']or x in ['Std','Lean']for x in imps))
 dst=S/(e['module']+'.lean');shutil.copyfile(canonical,dst)
 if e['adapter']:
  shutil.copyfile(original,O/(e['module']+'-producer.lean'))
 rows.append({**e,'canonical_source':str(canonical),'isolated_source':str(dst),'imports':imps})
add('102 unique ordered source inputs',len(rows)==102 and len(set(x['module']for x in rows))==102 and [x['module']for x in rows]==r['positive_order'])
for n,p in [('author-manifest.json',M),('canonical-author-certificate.json',R)]:shutil.copyfile(p,P/n)
out={'checks':checks,'denominator':len(checks),'passed':sum(z['pass']for z in checks),'all_pass':all(z['pass']for z in checks),'source_inputs':rows,'positive_order':r['positive_order'],'copied_scientific_oleans':0,'release_manifest_sha256':h(M),'canonical_receipt_sha256':h(R),'frozen_dependencies_only':True,'live_implementations_contacted':False,'replication_increment':0,'all_three_main_milestones':'OPEN'}
(P/'source-integrity-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['checks','source_inputs','positive_order']},indent=2))
assert out['all_pass']
