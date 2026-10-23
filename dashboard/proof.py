"""Read local campaign checkpoints; preserve observed revisions, never infer proof."""
import hashlib
import json
import time
from pathlib import Path

from catalog import ROOT

CAMPAIGN = ROOT / 'research/rmaf'
STATUSES = {'running', 'active', 'open', 'tested', 'refuted', 'checked', 'complete', 'conditional', 'pending', 'source-reported'}


class ProofObserver:
    def __init__(self, campaign=CAMPAIGN, history=None):
        self.campaign = Path(campaign).resolve()
        self.history = Path(history or ROOT / '.dashboard/proofs/rmaf.jsonl')
        self.hashes = {}
        self.records = []
        if self.history.is_file():
            for line in self.history.read_text().splitlines():
                try:
                    row = json.loads(line)
                    self.records.append(row)
                    self.hashes[row['id']] = row['hash']
                except (ValueError, KeyError, TypeError):
                    continue

    def snapshot(self):
        routes, errors = [], []
        try:
            spec = json.loads((self.campaign / 'spec.json').read_text())
        except (OSError, ValueError):
            return None
        for path in sorted((self.campaign / 'progress').glob('*.json')):
            try:
                if not path.resolve().is_relative_to(self.campaign):
                    raise ValueError('Outside campaign')
                raw = path.read_bytes()
                row = json.loads(raw)
                if not isinstance(row, dict) or not isinstance(row.get('id'), str) or row.get('status') not in STATUSES:
                    raise ValueError('Invalid checkpoint')
                if row['status'] == 'active':
                    row['reported_status'] = 'active'
                    row['status'] = 'running'
                # These are authored checkpoint claims, not independent dashboard certification.
                row['observed_at'] = path.stat().st_mtime
                routes.append(row)
                digest = hashlib.sha256(raw).hexdigest()
                if self.hashes.get(row['id']) != digest:
                    event = {'at': time.time(), 'id': row['id'], 'hash': digest, 'record': row}
                    self.history.parent.mkdir(parents=True, exist_ok=True)
                    with self.history.open('a') as out:
                        out.write(json.dumps(event, allow_nan=False) + '\n')
                    self.records.append(event)
                    self.hashes[row['id']] = digest
            except (OSError, ValueError, TypeError) as exc:
                errors.append({'file': path.name, 'error': str(exc)})
        return {'spec': spec, 'routes': routes, 'history': self.records[-60:], 'errors': errors,
                'at': time.time(), 'scope': 'reported checkpoints'}

    def read_file(self, name):
        path = (ROOT / name).resolve()
        if not path.is_relative_to(ROOT) or not path.is_relative_to(self.campaign) or not path.is_file():
            raise ValueError('Unknown campaign file')
        if path.suffix not in {'.json', '.jsonl', '.md', '.lean', '.py', '.txt', '.log', '.toml'}:
            raise ValueError('Unsupported evidence format')
        if path.stat().st_size > 1024 * 1024:
            raise ValueError('Evidence exceeds preview limit; open local file')
        return {'path': str(path.relative_to(ROOT)), 'text': path.read_text()}
