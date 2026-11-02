"""Guard against stale reviewer links after source and documentation edits."""
from pathlib import Path
import tempfile
import unittest

from check_paper_links import link_errors


class PaperLinksTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / 'Example.lean'
        self.source.write_text('theorem result : True := trivial\n')
        self.guide = self.root / 'README.md'

    def test_correct_declaration_link(self):
        self.guide.write_text('[`result`](Example.lean#L1)\n')
        self.assertEqual(link_errors(self.guide), [])

    def test_moved_declaration_is_rejected(self):
        self.guide.write_text('[`result`](Example.lean#L1)\n')
        self.source.write_text('-- A new explanation.\ntheorem result : True := trivial\n')
        self.assertTrue(link_errors(self.guide))

    def test_wrong_declaration_is_rejected(self):
        self.guide.write_text('[`different_result`](Example.lean#L1)\n')
        self.assertTrue(link_errors(self.guide))

    def test_missing_file_is_rejected(self):
        self.guide.write_text('[Proof](Missing.lean)\n')
        self.assertTrue(link_errors(self.guide))

    def test_missing_heading_is_rejected(self):
        (self.root / 'PROOFS.md').write_text('# Soundness\n')
        self.guide.write_text('[Proof](PROOFS.md#completeness)\n')
        self.assertTrue(link_errors(self.guide))


if __name__ == '__main__':
    unittest.main()
