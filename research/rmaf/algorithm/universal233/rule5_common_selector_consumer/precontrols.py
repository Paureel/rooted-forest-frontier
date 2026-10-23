#!/usr/bin/env python3
"""Fresh Std-only detector plants before scientific source application."""
from pathlib import Path
import datetime,gzip,hashlib,json,sys
sys.dont_write_bytecode=True
import instrument,pilot
D=Path(__file__).resolve().parent;R=D.parents[4];O=R/'results'/('algorithm-universal233-rule5-common-selector-producer-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir();(O/'lean-toolchain').write_bytes((D/'build/lean-toolchain').read_bytes())
mods={'CleanA':'theorem Shared : True := True.intro\n','CleanB':'theorem Shared : True := True.intro\ndef data : Nat := 3\nopaque op : Nat := 7\n','Hostile':'axiom Shared : True\ntheorem own : True := True.intro\n','Private':'private axiom hidden : False\n','OpaqueHostile':'axiom evil : Nat\nnoncomputable opaque used : Nat := evil\n','Carrier':'namespace Carrier\naxiom secret : False\naxiom secretNat : Nat\nend Carrier\n','ProofDependent':'import Carrier\ntheorem proofHidden : False := Carrier.secret\n','OpaqueDependent':'import Carrier\nnoncomputable opaque opaqueHidden : Nat := Carrier.secretNat\n'}
for n,s in mods.items():(O/(n+'.lean')).write_text('import Std\n'+s);pilot.run(O,n,True)
controls={}
for tag,ns,hostile in [('clean',['CleanA','CleanB'],False),('coalesced',['CleanA','Hostile'],True),('private',['Private'],True),('opaque',['OpaqueHostile'],True),('proof_dependency',['ProofDependent'],True),('opaque_dependency',['OpaqueDependent'],True)]:
 F=O/('records-'+tag);F.mkdir();(O/(tag+'.lean')).write_text(instrument.source(ns,ns,F));pilot.run(O,tag,want=1 if hostile else 0);rows=instrument.parse(F,ns,O,hostile);controls[tag]={'status':'CAUGHT' if hostile else 'PASS','rows':len(rows)}
 if tag=='clean':
  shared=[r for r in rows if r['name']=='Shared'];assert len(shared)==2
  assert any(r['kind']=='opaque' and r['body'] is not None for r in rows)
  idx=F/'index.json';original=idx.read_bytes();j=json.loads(original);j['counts'][0]['path']='/tmp/foreign/CleanA.olean';idx.write_text(json.dumps(j))
  try:instrument.parse(F,ns,O)
  except AssertionError:controls['foreign_path']='CAUGHT'
  else:raise AssertionError('FOREIGN_PATH_SURVIVED')
  idx.write_bytes(original)
  p=F/'CleanA.json.gz';original=p.read_bytes()
  for label,mut in [('missing',[]),('duplicate',shared[:1]+shared[:1])]:
   with gzip.open(p,'wt') as f:json.dump(mut,f)
   try:instrument.parse(F,ns,O)
   except AssertionError:controls[label]='CAUGHT'
   else:raise AssertionError(label)
  p.write_bytes(original)
for n,s,w in [('StdTrue','example : (3:Nat)+4=7 := by decide\n',0),('StdFalse','example : (3:Nat)+4=8 := by decide\n',1)]:
 (O/(n+'.lean')).write_text('import Std\n'+s);txt=pilot.run(O,n,want=w)
 if w:assert txt.count('is false')==1
rec={'status':'PASS_FRESH_STD_PRODUCER_CONTROLS','controls':controls,'independent_credit':0,'instrument_sha256':hashlib.sha256((D/'instrument.py').read_bytes()).hexdigest(),'scope':'Theorem proof text omitted; actual full ConstantInfo proof references and AX closure walked. All nonproof/opaque bodies retained.','immutable_files':[{'path':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(O.rglob('*')) if p.is_file()]}
M=O/'manifest.json';M.write_text(json.dumps(rec,indent=2)+'\n')
for p in O.rglob('*'):
 if p.is_file():p.chmod(0o444)
(D/'PRODUCER-PREFLIGHT-v1.json').write_text(json.dumps({'manifest':str(M.relative_to(R)),'sha256':hashlib.sha256(M.read_bytes()).hexdigest()},indent=2)+'\n');print(rec['status'],O)
