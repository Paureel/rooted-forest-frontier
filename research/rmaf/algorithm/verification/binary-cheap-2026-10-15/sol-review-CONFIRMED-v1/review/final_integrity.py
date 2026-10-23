#!/usr/bin/env python3
"""Final pinned-file/preservation verification only; no mathematical rerun."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
def h(p):
 d=hashlib.sha256()
 with p.open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
checks=[]
def add(n,v):checks.append({'name':n,'pass':bool(v)})
olds=[('research/rmaf/algorithm/verification/binary-cheap-2026-10-15/sol-preparation-READY-v1',90,'bcfc36f9c371ba5949ca30a37dc9ccd590cd98fbbca29787fde83288cd9ed12c','fc5d6ea1ac6b79f621c7c6d41b5709c9e5c902bb615a6150455f22b13340c30b'),('research/rmaf/algorithm/verification/good-pair-consumer-2026-10-15/sol-review-CONFIRMED-v1',213,'30c9c5d829cda6999fd4c2ba40eb34256996252690952b63f8289a9efaa7ce46','86ed5a198689f751072e6b479a67473aaf8c55292500812c6e76c49d39a7218f'),('research/rmaf/algorithm/verification/good-pair-consumer-2026-10-15/sol-preparation-READY-v1',109,'ccace5653dd25e1844e8477ef09c6b0b3e5f31ad2d555392cb9dc97bf9d34b3a','e4cd9e45d7f97465b494b5fb0e6ad6398a0582a28c4612e03c2bce438c024570'),('research/rmaf/algorithm/pair_case/cheap_high/x0/sol-handoff-v1',36,'4bf3403507f3ce517b1e3010de4c581fbd202afdf579f7c77300b1dc26562d3b','a6f04044562895cbd8343b64b8e507d8e3bc633cd8f1df03bc3fd0eb8942f216')]
oldrows=[]
for rel,n,msha,asha in olds:
 d=ROOT/rel;m=json.loads((d/'MANIFEST.json').read_text());bad=[]
 for e in m['entries']:
  f=d/e['path']
  if not f.is_file()or f.stat().st_size!=e['bytes']or h(f)!=e['sha256']:bad.append(e['path'])
 good=len(m['entries'])==n and not bad and h(d/'MANIFEST.json')==msha and h(Path(str(d)+'.tar.gz'))==asha;add(rel+' preservation',good);oldrows.append({'path':rel,'entries':len(m['entries']),'manifest_sha256':h(d/'MANIFEST.json'),'archive_sha256':h(Path(str(d)+'.tar.gz')),'bad_entries':bad,'all_pass':good})
author=json.loads((P/'author-manifest.json').read_text());bad=[]
for e in author['immutable_files']:
 f=ROOT/e['path']
 if not f.is_file()or f.stat().st_size!=e['bytes']or h(f)!=e['sha256']:bad.append(e['path'])
add('all280 released author entries unchanged',len(author['immutable_files'])==280 and not bad);add('exact author manifest unchanged',h(ROOT/'research/rmaf/algorithm/universal233/binary_cheap/BINARY-CHEAP-MANIFEST-v1.json')=='3936cb4b0a5d390972ad7b1fdace4166faa9a372cc9232329294a0f2b346d839')
info=json.loads((P/'source-integrity-v1.json').read_text())
for r in info['source_inputs']:add(r['module']+' exact isolated source unchanged',h(P/'src'/(r['module']+'.lean'))==r['compiled_sha256'])
required=['compiled-primitive-comparison-v1.json','compiled-pilot-comparison-v1.json','compiled-battery-comparison-v1.json','compiled-separation-comparison-v1.json','final-literal-malformed-pin-controls-v1.json','audit-pilot-comparison-v1.json','audit-planted-comparison-v1.json','audit-scientific-comparison-v1.json','fingerprint-toy-comparison-v2.json','producer-data-controls-comparison-v1.json','producer-data-scientific-comparison-v1.json','producer-adoption-comparison-v4.json','producer-source-adapter-v1.json','actual-imported-dependency-identity-v1.json','consumer-interface-trace-v1.json']
for n in required:add(n+' successful required check',json.loads((P/n).read_text())['all_pass'])
scan=json.loads((P/'full-source-escape-scan-v1.json').read_text());add('source escape scan only two classified comments',[(r['module'],r['line'])for r in scan['hits']]==[('CoreGraph',175),('Normalization',202)])
# Native whole-source same-address observation versus independent original graph cut; exact restricted cut is different.
import importlib.util
R=P.parent/'sol-preparation-READY-v1/preparation';sp=importlib.util.spec_from_file_location('owned_graph',R/'instrument/x0_evaluator_reused.py');x=importlib.util.module_from_spec(sp);sp.loader.exec_module(x);f=json.loads((R/'fixtures-v1.json').read_text())['fixtures'][0];sep=json.loads((P/'compiled-separation-comparison-v1.json').read_text())['observation'];cp=x.Graph(f['S']).cut_parts(['0']);native=sep['whole_source_same_address_partition'];add('native whole-source same-address forest matches original graph',x.canon(native)==cp['parts']);pilot=json.loads((P/'compiled-pilot-comparison-v1.json').read_text())['observations'][0];local=pilot['local_A']['result']['partition'];projection=[set(b)&set(f['P'][0])for b in native if set(b)&set(f['P'][0])];add('native whole-source local-address projection differs from local certificate',x.canon(projection)!=x.canon(local))
out={'checks':checks,'denominator':len(checks),'passed':sum(z['pass']for z in checks),'all_pass':all(z['pass']for z in checks),'preserved':oldrows,'author_bad_entries':bad,'all_three_main_milestones':'OPEN','replication_increment':0,'no_mathematical_rerun':True};(P/'final-input-and-preservation-integrity-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['checks','preserved']},indent=2));assert out['all_pass']
