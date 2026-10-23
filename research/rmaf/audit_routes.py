"""Campaign-specific replay of auxiliary proofs; no general rMAF theorem implied."""
import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CAMPAIGN = ROOT / 'research/rmaf'
OUT = CAMPAIGN / 'audit'
MODULES = [('Baseline', 'audit/Baseline.lean'), ('Branching', 'branching/Certificates.lean'),
           ('Decomposition', 'decomposition/IndependentMinima.lean')]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def main():
    OUT.mkdir(exist_ok=True)
    env = dict(os.environ, ELAN_HOME=str(ROOT / '.runtime/elan'))
    certificates = []
    for title, relative in MODULES:
        path = CAMPAIGN / relative
        source = path.read_bytes()
        result = subprocess.run([str(ROOT / '.runtime/elan/bin/lean'), str(path)], env=env,
                                capture_output=True, text=True, timeout=90)
        output = result.stdout + result.stderr
        log = OUT / (title.lower() + '.log')
        log.write_text(output)
        theorem_rows = []
        for line in output.splitlines():
            match = re.match(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[(.*)\])", line)
            if match:
                axioms = [a.strip() for a in (match.group(3) or '').split(',') if a.strip()]
                theorem_rows.append({'theorem': match.group(1), 'axioms': axioms,
                                     'allowed_only': set(axioms) <= ALLOWED})
        if result.returncode or not theorem_rows or not all(t['allowed_only'] for t in theorem_rows) or 'warning:' in output:
            raise RuntimeError('Failed proof or axiom audit: ' + relative)
        certificates.append({'module': relative, 'source_sha256': hashlib.sha256(source).hexdigest(),
                             'exit_code': result.returncode, 'theorems': theorem_rows,
                             'log': str(log.relative_to(ROOT))})
        print(f'{title}: {len(theorem_rows)} checked theorem declarations', flush=True)
    record = {'at': time.time(), 'lean_version': '4.35.0', 'modules': certificates,
              'scope': 'Auxiliary arithmetic, generic composition and counting only. Structural MAF obligations remain open.'}
    (OUT / 'certificate.json').write_text(json.dumps(record, indent=2) + '\n')

if __name__ == '__main__':
    main()
