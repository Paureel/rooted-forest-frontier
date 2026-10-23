#!/usr/bin/env python3
"""Raw producer ModuleData controls; independently catches merged-origin coalescing."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;S=P/'src'
body='''import ModuleDataAudit
namespace ProducerToy
def ordinary : Nat := 7
theorem harmless : True := True.intro
end ProducerToy
'''
for n in ['ProducerToyA','ProducerToyB','ProducerToyBad']:
 (S/(n+'.lean')).write_text(body+('private axiom unused_bad : False\n'if n=='ProducerToyBad'else''))
(S/'AuditProducerDataControls.lean').write_text('import ModuleDataAudit\nimport ProducerToyA\nimport ProducerToyB\nimport ProducerToyBad\nimport ToyClean\nimport ToyUnused\nimport ToyPrivate\nimport ToyUseExternal\nrun_cmd ProducerDataAudit.emit ["ProducerToyA","ProducerToyB","ProducerToyBad","ToyClean","ToyUnused","ToyPrivate","ToyUseExternal"]\n')
mods=json.loads((P/'source-integrity-v1.json').read_text())['positive_order']
(S/'AuditEveryProducer.lean').write_text('import ModuleDataAudit\n'+''.join('import '+m+'\n'for m in mods)+'run_cmd ProducerDataAudit.emit '+json.dumps(mods)+'\n')
(P/'module-data-audit-freeze-v1.json').write_text(json.dumps({'before_execution':True,'source_sha256':hashlib.sha256((S/'ModuleDataAudit.lean').read_bytes()).hexdigest(),'expected_controls':{'ProducerToyA':{'count':2,'accept':True},'ProducerToyB':{'count':2,'accept':True},'ProducerToyBad':{'count':3,'accept':False},'ToyClean':{'count':19,'accept':True},'ToyUnused':{'count':2,'accept':False},'ToyPrivate':{'count':19,'accept':False},'ToyUseExternal':{'count':1,'accept':False}},'expected_duplicate_origin_occurrences':4,'missing_or_duplicate_entry_rejects':True,'basis':'Lean.Environment header.moduleData contains each imported producer constant array before name coalescing; imports const2ModIdx uses insertIfNew. Direct CI kind and own type/value dependencies are audited.','source_API':'Lean/Environment.lean:109-129,142-176,2314-2360; Lean/Util/CollectAxioms.lean','mathematical_fixture_expectations_changed':False},indent=2)+'\n');print('Stored-module audit and duplicate-origin/unused-axiom toy expectations frozen.')
