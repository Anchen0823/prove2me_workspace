"""Regression checks for mission build isolation; no Lean or network required."""
import contextlib
import io
import json
import subprocess
import unittest
from unittest.mock import patch

import workspace


class MissionIsolationTests(unittest.TestCase):
    def test_every_mission_has_a_valid_scope(self):
        missions = json.loads((workspace.ROOT / 'missions/index.json').read_text(encoding='utf-8'))['missions']
        self.assertEqual(workspace.check(missions), 0)

    def test_unrelated_tasks_have_disjoint_build_roots(self):
        tasks = ['no-adjacent', 'zudilin', 'two-squares', 'bunkbed',
                 'magic-squares', 'semi-magic', 'normal3', 'magic-squares-iv',
                 'magic-squares-v', 'five-primes', 'euler-gamma', 'weak-goldbach']
        seen = set()
        for slug in tasks:
            targets = set(workspace.build_targets(workspace.read_scope(slug)))
            self.assertTrue(targets, slug)
            self.assertFalse(seen & targets, slug)
            seen |= targets

    def test_dry_run_never_starts_lake(self):
        with patch.object(workspace.subprocess, 'run') as run, contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(workspace.build_mission({'slug': 'no-adjacent'}, True), 0)
        run.assert_not_called()

    def test_research_task_cannot_fall_back_to_default_build(self):
        with patch.object(workspace.subprocess, 'run') as run, contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(workspace.build_mission({'slug': 'fgh-scout'}), 0)
        run.assert_not_called()

    def test_build_uses_exact_targets_and_propagates_failure(self):
        with patch.object(workspace, 'lake_environment', return_value=('lake', {})), \
             patch.object(workspace.subprocess, 'run', return_value=subprocess.CompletedProcess([], 7)) as run, \
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(workspace.build_mission({'slug': 'two-squares'}), 7)
        self.assertEqual(run.call_args.args[0], [
            'lake', 'build', 'examples/two-squares/Family.lean', 'examples/two-squares/Identity.lean'])
        self.assertEqual(run.call_args.kwargs['cwd'], workspace.ROOT)

    def test_missing_or_escaping_patterns_fail_before_build(self):
        for pattern in ['../outside/*.lean', 'Solutions/does-not-exist.lean']:
            with self.assertRaises(ValueError):
                workspace.build_targets({'build': [pattern]})


if __name__ == '__main__':
    unittest.main()
