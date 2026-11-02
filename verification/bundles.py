"""Read and validate data-only public-result export bundles."""
import hashlib
import json
from pathlib import Path
import shutil
import tarfile

ROOT_MODULE = 'DistributedSynthesis.Results'
FIELDS = ('format', 'module', 'result_modules', 'theorem_names', 'rigid_names')


def validate_manifest(manifest):
    if manifest.get('format') != 1 or manifest.get('module') != ROOT_MODULE:
        raise ValueError('Unsupported public-result bundle format or root module')
    for field in FIELDS[2:]:
        values = manifest.get(field)
        if not isinstance(values, list) or any(not isinstance(x, str) or not x for x in values):
            raise ValueError(f'Invalid {field}')
        if values != sorted(set(values)):
            raise ValueError(f'{field} must be sorted and contain no duplicates')
    if ROOT_MODULE not in manifest['result_modules'] or not manifest['theorem_names']:
        raise ValueError('Empty public-result coverage')
    if set(manifest['theorem_names']) & set(manifest['rigid_names']):
        raise ValueError('Overlapping theorem and fixed-definition inventories')


def check_result_modules(project, manifest):
    """Catch new source modules omitted from the Results import umbrella."""
    expected = {ROOT_MODULE}
    expected.update('.'.join(path.relative_to(project).with_suffix('').parts)
                    for path in (project / 'DistributedSynthesis/Results').rglob('*.lean'))
    missing = expected - set(manifest['result_modules'])
    if missing:
        raise ValueError('Public result modules absent from the compiled API: ' + ', '.join(sorted(missing)))


def write_bundle(manifest_path, declarations, output):
    manifest = json.loads(manifest_path.read_text())
    validate_manifest(manifest)
    with declarations.open('rb') as handle:
        manifest['sha256'] = hashlib.file_digest(handle, 'sha256').hexdigest()
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    with tarfile.open(fileobj=output, mode='w|') as archive:
        archive.add(manifest_path, arcname='manifest.json')
        archive.add(declarations, arcname='declarations.ndjson')


def read_bundle(bundle, destination):
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tarfile.open(bundle, mode='r:') as archive:
        members = archive.getmembers()
        if sorted(member.name for member in members) != ['declarations.ndjson', 'manifest.json']:
            raise ValueError('Bundle must contain exactly manifest.json and declarations.ndjson')
        if any(not member.isfile() for member in members):
            raise ValueError('Bundle members must be regular files')
        if archive.getmember('manifest.json').size > 32 * 1024 * 1024:
            raise ValueError('Oversized bundle manifest')
        with archive.extractfile('manifest.json') as handle:
            manifest = json.load(handle)
        validate_manifest(manifest)
        with archive.extractfile('declarations.ndjson') as source, destination.open('wb') as target:
            shutil.copyfileobj(source, target)
    with destination.open('rb') as handle:
        digest = hashlib.file_digest(handle, 'sha256').hexdigest()
    if manifest.get('sha256') != digest:
        raise ValueError('Bundle declaration hash mismatch')
    return manifest


def matching_coverage(reference, solution):
    for field in FIELDS:
        if reference[field] != solution[field]:
            raise ValueError(f'Public-result coverage changed ({field}); review the API and create a new reference')
