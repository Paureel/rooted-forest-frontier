#!/usr/bin/env python3
"""Lean/Std-only true/body-false twins for auxiliary producer type/value fingerprints."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
body='''import FingerprintSupport
namespace FingerprintToy
structure Packet where
  value : Nat
private def hidden : Nat := 7
def projected (r : Packet) : Nat := r.value + hidden
theorem harmless : True := True.intro
end FingerprintToy
'''
rows=[]
for n in ['FingerprintToyClean','FingerprintToyTwin','FingerprintToyBad']:
 s=body if n!='FingerprintToyBad'else body.replace('r.value + hidden','r.value + hidden + 1')
 f=P/'src'/(n+'.lean');f.write_text(s+'\nrun_cmd ProducerFingerprint.emit ["'+n+'"]\n');rows.append({'module':n,'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
(P/'fingerprint-control-freeze-v1.json').write_text(json.dumps({'before_toy_execution_and_adoption_comparison':True,'auxiliary_scientific_fingerprint_collection_already_occurred':True,'sequence_boundary':'Primary body/import gate was frozen and planted-tested in READY; new Expr metadata is supplemental and is not independent evidence','sources':rows,'expected_clean_count':19,'expected_clean_twin_equal':True,'expected_bad_names_types_equal':True,'expected_bad_value_equal':False,'expected_missing_duplicate_empty_rejected':True},indent=2)+'\n');print('Supplemental fingerprint toy twins frozen; scientific fixture expectations unchanged.')
