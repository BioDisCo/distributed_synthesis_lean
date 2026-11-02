"""Host-side failure handling; the Docker self-test exercises the real kernels."""
import argparse
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import verify


class AuditCommands(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.reference = self.root / 'reference.ndjson'
        self.solution = self.root / 'solution.ndjson'
        self.reference.write_text('reference')
        self.solution.write_text('solution')
        self.args = argparse.Namespace(reference=self.reference, solution=self.solution,
                                       image='test-audit', jobs=2, kernels='lean')

    def test_same_path_is_rejected(self):
        self.args.solution = self.reference
        with self.assertRaisesRegex(ValueError, 'separate files'):
            verify.comparison_command(self.args)

    def test_empty_export_is_rejected(self):
        self.solution.write_text('')
        with self.assertRaisesRegex(ValueError, 'empty export'):
            verify.comparison_command(self.args)

    def test_comparison_has_only_readonly_inputs_and_no_network(self):
        command = verify.comparison_command(self.args)
        for flag in ('--network=none', '--cap-drop=ALL', '--security-opt=no-new-privileges', '--read-only'):
            self.assertIn(flag, command)
        mounts = [command[i + 1] for i, flag in enumerate(command)
                  if flag == '--mount' and command[i + 1].startswith('type=bind,')]
        self.assertEqual(len(mounts), 2)
        self.assertTrue(all(value.endswith(',readonly') for value in mounts))
        self.assertFalse(any('docker.sock' in value for value in command))

    @patch.object(verify, 'run')
    def test_checker_failure_propagates(self, run):
        run.side_effect = subprocess.CalledProcessError(1, 'checker')
        with self.assertRaises(subprocess.CalledProcessError):
            verify.compare(self.args)

    @patch.object(verify, 'run')
    def test_reference_cannot_be_overwritten(self, run):
        self.args.output = self.reference
        self.args.project = self.root
        with self.assertRaisesRegex(ValueError, 'overwrite'):
            verify.export(self.args)
        run.assert_not_called()
        self.assertEqual(self.reference.read_text(), 'reference')

    @patch.object(verify, 'run')
    def test_failed_export_does_not_publish_and_removes_volume(self, run):
        self.args.output = self.root / 'new.ndjson'
        self.args.project = self.root
        run.side_effect = [None, subprocess.CalledProcessError(1, 'export'), None]
        with self.assertRaises(subprocess.CalledProcessError):
            verify.export(self.args)
        self.assertFalse(self.args.output.exists())
        self.assertEqual(run.call_args_list[-1].args[0][:3], ['docker', 'volume', 'rm'])
        self.assertFalse(list(self.root.glob('*.partial')))

    @patch.object(verify, 'run')
    def test_fast_stops_on_build_failure(self, run):
        run.side_effect = [None, subprocess.CalledProcessError(1, 'lake')]
        with self.assertRaises(subprocess.CalledProcessError):
            verify.fast(self.args)
        self.assertEqual(run.call_count, 2)
        run.assert_called_with(['lake', '--wfail', 'build'], cwd=verify.ROOT)

    @patch.object(verify, 'build')
    def test_check_requires_reference_before_building(self, build):
        self.reference.unlink()
        with self.assertRaisesRegex(ValueError, 'reviewed reference'):
            verify.check(self.args)
        build.assert_not_called()

    @patch.object(verify, 'build')
    def test_reference_refuses_overwrite_before_building(self, build):
        self.args.output = self.reference
        with self.assertRaisesRegex(ValueError, 'overwrite'):
            verify.reference(self.args)
        build.assert_not_called()

    def test_check_sequences_operations_and_cleans_up_after_failure(self):
        # CLI check has no solution argument: it must generate its own candidate.
        del self.args.solution
        events = []
        candidates = []

        def export(args):
            events.append('export')
            args.output.write_text('candidate')
            candidates.append(args.output)

        def compare(args):
            events.append('compare')
            self.assertEqual(args.reference, self.reference)
            self.assertEqual(args.solution.read_text(), 'candidate')
            raise subprocess.CalledProcessError(1, 'checker')

        with patch.object(verify, 'build', side_effect=lambda _: events.append('build')), \
             patch.object(verify, 'export', side_effect=export), \
             patch.object(verify, 'compare', side_effect=compare):
            with self.assertRaises(subprocess.CalledProcessError):
                verify.check(self.args)
        self.assertEqual(events, ['build', 'export', 'compare'])
        self.assertFalse(candidates[0].parent.exists())
        self.assertEqual(self.reference.read_text(), 'reference')


if __name__ == '__main__':
    unittest.main()
