from fractions import Fraction
from pathlib import Path
import json
b=Path(__file__).resolve().parent;c=Fraction(233,100)
terms={'clique':2/c+3/c**4,'chain':2/c+4/c**4,'diagonal':2/c+1/c**3+1/c**4}
assert all(x<1 for x in terms.values()) and 2<c<Fraction(23391,10000)
assert not(Fraction(101,100)<1)
x={'phase':'supplemental independent exact arithmetic, not a new replication or global recurrence acceptance','base':'233/100','complete_displayed_factors':{k:str(v) for k,v in terms.items()},'strict_slacks':{k:str(1-v) for k,v in terms.items()},'false_factor_101_over_100':'REJECTED','scope':'Conditional arithmetic only; actual state,decreasing budgets,query scheduling,size invariants,termination and reconstruction remain OPEN'}
(b/'RATIONAL-MARGIN-CHECK.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x))
