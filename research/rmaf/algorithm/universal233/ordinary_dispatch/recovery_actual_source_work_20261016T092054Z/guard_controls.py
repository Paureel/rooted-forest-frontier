#!/usr/bin/env python3
"""One-shot no-rebuild guard control; no compiler is launched for these names."""
import json
import run
out=[]
for n in ['CoreProgram','Work','BOOptimize','OWOptimize']:
 try:run.run(n)
 except AssertionError as e:
  assert str(e)=='REFUSE_DEPENDENCY_REBUILD|'+n
  out.append({'module':n,'result':str(e),'compiler_started':False})
 else:raise AssertionError('DEPENDENCY_GUARD_FAILED|'+n)
(run.D/'DEPENDENCY-GUARD-v1.json').write_text(json.dumps({'rejections':out,'clean_allowed_control':'RWControls exact successful source/receipt already retained','dependency_rebuilds':0},indent=2)+'\n')
print('PASS_NO_REBUILD_GUARD',len(out))
