"""One-shot adverse premise test, not an in-regime source branch."""
import json
from pathlib import Path
from finite_check import parse,mark,lookup,cut,allowed
f=parse('(a,(x,y))');mark(f,['a','x,y'])
assert all(allowed(lookup(f,x)) for x in ['x','y'])
g=cut(f,['x','y']);a=lookup(g,'a')
assert a.sibling() is None
out={'claim':'arbitrary legal simultaneous cuts preserve the protected sibling','verdict':'false outside the source prescribed-cut regime','before':'((a,(x,y)))rho','protected':['a','x,y'],'cuts':['x','y'],'after':[t.text() for t in g],'reason_outside_regime':'No Chapter 6 branch cuts both endpoints of a sibling pair; (x,y) is already a common cherry in this minimal fixture.','source_history_status':'not refuted; must exploit branch shape to exclude total erasure of b'}
Path('research/rmaf/results/thesis-runtime-repair-adversary-history-premise.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
