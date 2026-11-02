import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

from bundles import check_result_modules, matching_coverage, read_bundle, write_bundle


class PublicCoverage(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.manifest = {'format': 1, 'module': 'DistributedSynthesis.Results',
                         'result_modules': ['DistributedSynthesis.Results'],
                         'theorem_names': ['Example.result'], 'rigid_names': ['Example.model']}

    def bundle(self):
        manifest = self.root / 'manifest.json'
        manifest.write_text(json.dumps(self.manifest))
        declarations = self.root / 'declarations.ndjson'
        declarations.write_text('test declaration data\n')
        bundle = self.root / 'export.tar'
        with bundle.open('wb') as out:
            write_bundle(manifest, declarations, out)
        return bundle

    def test_roundtrip(self):
        destination = self.root / 'unpacked.ndjson'
        result = read_bundle(self.bundle(), destination)
        matching_coverage(self.manifest, result)
        self.assertEqual(destination.read_text(), 'test declaration data\n')

    def test_added_or_removed_result_cannot_be_omitted(self):
        for names in ([], ['Example.new', 'Example.result']):
            with self.subTest(names=names), self.assertRaisesRegex(ValueError, 'coverage changed'):
                matching_coverage(self.manifest, {**self.manifest, 'theorem_names': names})

    def test_fixed_definition_inventory_is_enforced(self):
        with self.assertRaisesRegex(ValueError, 'coverage changed'):
            matching_coverage(self.manifest, {**self.manifest, 'rigid_names': []})

    def test_unimported_public_module_is_rejected(self):
        path = self.root / 'DistributedSynthesis/Results/NewResult.lean'
        path.parent.mkdir(parents=True)
        path.write_text('')
        with self.assertRaisesRegex(ValueError, 'NewResult'):
            check_result_modules(self.root, self.manifest)

    def test_payload_corruption_is_rejected(self):
        bundle = self.bundle()
        bundle.write_bytes(bundle.read_bytes().replace(b'test declaration data', b'fake declaration data'))
        with self.assertRaisesRegex(ValueError, 'hash mismatch'):
            read_bundle(bundle, self.root / 'out.ndjson')

    def test_archive_links_are_rejected(self):
        path = self.root / 'link.tar'
        with tarfile.open(path, 'w') as out:
            member = tarfile.TarInfo('manifest.json')
            member.type = tarfile.SYMTYPE
            member.linkname = '/etc/passwd'
            out.addfile(member)
            member = tarfile.TarInfo('declarations.ndjson')
            member.size = 0
            out.addfile(member, io.BytesIO())
        with self.assertRaisesRegex(ValueError, 'regular files'):
            read_bundle(path, self.root / 'out.ndjson')


if __name__ == '__main__':
    unittest.main()
