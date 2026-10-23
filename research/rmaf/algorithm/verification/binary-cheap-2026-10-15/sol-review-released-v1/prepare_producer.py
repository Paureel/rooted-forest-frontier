#!/usr/bin/env python3
"""Exact registered source/import adapter checks and independent producer-origin view."""
from pathlib import Path
import hashlib,json,shutil
P=Path(__file__).resolve().parent;A=P/'producer-origin';S=A/'src';B=A/'build'
for p in [A,S,B]:p.mkdir(exist_ok=True)
if list(B.iterdir()):raise SystemExit('Producer build must begin empty')
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();checks=[]
def add(n,v):checks.append({'name':n,'pass':bool(v)})
old=P/'original-adapters/DepthRestriction-producer.lean';new=P/'src/DepthRestriction.lean';add('Restriction to DepthRestriction filename only',old.read_bytes()==new.read_bytes())
eold=(P/'original-adapters/Embedding-producer.lean').read_text();enew=(P/'src/Embedding.lean').read_text();expected=eold.replace('import Restriction\n','import DepthRestriction\n',1)
add('Embedding only exact first import substitution',enew==expected);add('only one registered import site',eold.count('import Restriction\n')==1)
add('all Embedding type and body bytes preserved',enew.split('\n',1)[1]==eold.split('\n',1)[1])
shutil.copyfile(old,S/'Restriction.lean');shutil.copyfile(P/'original-adapters/Embedding-producer.lean',S/'Embedding.lean')
(S/'AuditProducer.lean').write_text('import OriginAudit\nimport Embedding\nrun_cmd ReleasedAudit.emit ["Restriction","Embedding"]\n')
(S/'FingerprintProducer.lean').write_text('import FingerprintSupport\nimport Embedding\nrun_cmd ProducerFingerprint.emit ["Restriction","Embedding"]\n')
(P/'src/FingerprintCanonical.lean').write_text('import FingerprintSupport\nimport Embedding\nrun_cmd ProducerFingerprint.emit ["DepthRestriction","Embedding"]\n')
(P/'producer-source-adapter-v1.json').write_text(json.dumps({'checks':checks,'denominator':len(checks),'all_pass':all(z['pass']for z in checks),'frozen_before_producer_compile':True,
 'source_fingerprints':[{'path':str(p.relative_to(P)),'sha256':h(p)}for p in [old,new,P/'original-adapters/Embedding-producer.lean',P/'src/Embedding.lean',P/'src/FingerprintSupport.lean',P/'src/FingerprintCanonical.lean',S/'AuditProducer.lean',S/'FingerprintProducer.lean']],
 'registered_origin_map':{'Restriction':'DepthRestriction','Embedding':'Embedding'},'fingerprint_fields':['user_name','private','kind','type','value'],'expression_normalization':'Only private constant names map through Lean.privateToUserName?; no source-location or body rewrite','copied_scientific_oleans':0},indent=2)+'\n');print('Exact adapters',len(checks),'/',len(checks));assert all(z['pass']for z in checks)
