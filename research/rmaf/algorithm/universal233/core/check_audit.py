"""One-shot fail-closed checker for this candidate's complete Lean axiom log."""
from pathlib import Path
import re
import sys
here = Path(__file__).resolve().parent
expected = [s.removeprefix('#print axioms ') for s in (here / 'Audit.lean').read_text().splitlines()
            if s.startswith('#print axioms ')]
lines = Path(sys.argv[1]).read_text().splitlines()
seen = {}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for line in lines:
    if m := re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", line):
        name, raw = m.groups()
        axioms = set(raw.split(', ')) if raw else set()
    elif m := re.fullmatch(r"'([^']+)' does not depend on any axioms", line):
        name, axioms = m.group(1), set()
    else:
        continue
    assert name not in seen, ('duplicate audit result', name)
    assert axioms <= allowed, ('unaccepted axiom', name, axioms - allowed)
    seen[name] = axioms
assert set(seen) == set(expected), ('missing or extra audit', set(expected)-set(seen), set(seen)-set(expected))
assert len(seen) == 112, len(seen)
print(f'PASS: {len(seen)} / {len(expected)} declarations; only standard Lean axioms {sorted(allowed)}')
