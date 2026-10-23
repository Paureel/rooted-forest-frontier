"""Proof checkpoints preserve evidence scope, history, and local-file boundaries."""
import json
import tempfile
import unittest
from pathlib import Path

from proof import ProofObserver


class ProofTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.campaign = self.root / 'campaign'
        (self.campaign / 'progress').mkdir(parents=True)
        (self.campaign / 'spec.json').write_text(json.dumps({'title': 'Test', 'baseline': {'base': 2.3391}}))
        self.observer = ProofObserver(self.campaign, self.root / 'history.jsonl')

    def tearDown(self):
        self.tmp.cleanup()

    def checkpoint(self, status='open'):
        path = self.campaign / 'progress/route.json'
        path.write_text(json.dumps({'id': 'route', 'status': status, 'title': 'Candidate', 'claims': []}))
        return path

    def test_open_stays_open_and_history_survives_restart(self):
        self.checkpoint()
        one = self.observer.snapshot()
        self.assertEqual(one['routes'][0]['status'], 'open')
        self.assertEqual(len(one['history']), 1)
        self.assertEqual(len(self.observer.snapshot()['history']), 1)
        self.checkpoint('refuted')
        self.assertEqual(len(self.observer.snapshot()['history']), 2)
        restarted = ProofObserver(self.campaign, self.root / 'history.jsonl')
        self.assertEqual([r['record']['status'] for r in restarted.snapshot()['history']], ['open', 'refuted'])

    def test_partial_invalid_checkpoint_is_visible_and_retried(self):
        path = self.checkpoint()
        path.write_text('{"id":')
        snap = self.observer.snapshot()
        self.assertEqual(snap['routes'], [])
        self.assertEqual(len(snap['errors']), 1)
        self.checkpoint('tested')
        self.assertEqual(self.observer.snapshot()['routes'][0]['status'], 'tested')

    def test_known_activity_alias_does_not_become_proved(self):
        self.checkpoint('active')
        route = self.observer.snapshot()['routes'][0]
        self.assertEqual(route['status'], 'running')
        self.assertEqual(route['reported_status'], 'active')

    def test_file_preview_blocks_traversal_and_external_symlink(self):
        outside = self.root / 'outside.md'
        outside.write_text('outside')
        link = self.campaign / 'linked.md'
        link.symlink_to(outside)
        with self.assertRaises(ValueError):
            self.observer.read_file(str(outside))
        with self.assertRaises(ValueError):
            self.observer.read_file(str(link))
        valid = self.campaign / 'proof.lean'
        valid.write_text('example : True := True.intro')
        # Production file links must also live under the workspace root.
        with self.assertRaises(ValueError):
            self.observer.read_file(str(valid))


if __name__ == '__main__':
    unittest.main()
