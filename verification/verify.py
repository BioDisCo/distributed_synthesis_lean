#!/usr/bin/env python3
"""Run fast library checks or Docker Comparator verification against a saved reference."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import uuid

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def run(args, **kwargs):
    print('+ ' + ' '.join(map(str, args)), file=sys.stderr, flush=True)
    return subprocess.run(list(map(str, args)), check=True, **kwargs)


def mount(path, target):
    path = Path(path).resolve(strict=True)
    if ',' in str(path):
        raise ValueError('Docker mount paths containing commas are not supported')
    return ['--mount', f'type=bind,source={path},target={target},readonly']


def isolation():
    # Do not mount the Docker socket, credentials, host caches, or writable source.
    return ['--network=none', '--cap-drop=ALL', '--security-opt=no-new-privileges',
            '--read-only', '--pids-limit=256',
            '--tmpfs', '/tmp:rw,nosuid,nodev,size=1g,uid=1000,gid=1000']


def build(args):
    for target in ('checker', 'proof'):
        run(['docker', 'build', '-f', HERE / 'Dockerfile', '--target', target,
             '-t', f'{args.image}-{target}', ROOT])


def fast(args):
    run([sys.executable, ROOT / 'scripts/check_paper_links.py'], cwd=ROOT)
    run(['lake', '--wfail', 'build'], cwd=ROOT)
    run([sys.executable, ROOT / 'scripts/check_library.py', '--axioms'], cwd=ROOT)
    run([sys.executable, ROOT / 'scripts/check_library.py', '--axioms',
         'DistributedSynthesis/Tests/ComponentTrees/Audit.lean'], cwd=ROOT)
    run([sys.executable, ROOT / 'scripts/check_library.py', '--axioms',
         'DistributedSynthesis/Tests/Undecidability/Audit.lean'], cwd=ROOT)
    run([sys.executable, ROOT / 'scripts/check_library.py', '--axioms',
         'DistributedSynthesis/Tests/Paper/Audit.lean'], cwd=ROOT)


def reference(args):
    if args.output.resolve().exists():
        raise ValueError(f'Refusing to overwrite an existing reference: {args.output}')
    build(args)
    export(args)


def check(args):
    # Validate the reference before preparing Docker or compiling the candidate.
    if not args.reference.is_file() or args.reference.stat().st_size == 0:
        raise ValueError(f'Missing or empty reviewed reference: {args.reference}')
    build(args)
    with tempfile.TemporaryDirectory(prefix='public-result-check-') as directory:
        candidate = Path(directory) / 'solution.tar'
        export(argparse.Namespace(**vars(args), output=candidate))
        compare(argparse.Namespace(**vars(args), solution=candidate))


def export(args):
    output = args.output.resolve()
    if output.exists():
        raise ValueError(f'Refusing to overwrite an existing export: {output}')
    output.parent.mkdir(parents=True, exist_ok=True)
    volume = 'distributed-synthesis-audit-' + uuid.uuid4().hex
    run(['docker', 'volume', 'create', volume], stdout=subprocess.DEVNULL)
    try:
        with tempfile.NamedTemporaryFile(dir=output.parent, suffix='.partial') as result:
            run(['docker', 'run', '--rm', *isolation(),
                 '--env', f'LEAN_NUM_THREADS={args.jobs}',
                 *mount(args.project, '/source'),
                 '--mount', f'type=volume,source={volume},target=/work',
                 f'{args.image}-proof'], stdout=result)
            result.flush()
            # Atomic, exclusive publication; failures never leave a partial reference.
            os.link(result.name, output)
        with output.open('rb') as saved:
            digest = hashlib.file_digest(saved, 'sha256').hexdigest()
        print(json.dumps({'export': str(output), 'sha256': digest}), flush=True)
    finally:
        run(['docker', 'volume', 'rm', volume], stdout=subprocess.DEVNULL)


def comparison_command(args):
    if args.reference.resolve() == args.solution.resolve():
        raise ValueError('Reference and solution must be separate files; a self-comparison is not a statement-preservation check')
    for path in (args.reference, args.solution):
        if not path.is_file() or path.stat().st_size == 0:
            raise ValueError(f'Missing or empty export: {path}')
    return ['docker', 'run', '--rm', *isolation(),
         '--env', f'LEAN_NUM_THREADS={args.jobs}',
         *mount(args.reference, '/reference.tar'),
         *mount(args.solution, '/solution.tar'),
         '--mount', 'type=volume,target=/work', f'{args.image}-checker', args.kernels]


def compare(args):
    run(comparison_command(args))


def self_test(args):
    args.kernels = 'both'
    with tempfile.TemporaryDirectory(prefix='proof-audit-tests-') as temp:
        directory = Path(temp)
        archive_path = directory / 'fixtures.tar'
        with archive_path.open('wb') as handle:
            run(['docker', 'run', '--rm', *isolation(),
                 '--tmpfs', '/work:rw,nosuid,nodev,size=128m,uid=1000,gid=1000',
                 '--entrypoint', 'python3', f'{args.image}-proof',
                 '/opt/audit/container.py', 'fixtures'], stdout=handle)
        labels = ('reference', 'valid', 'changed-definition', 'unused-definition',
                  'forbidden-axiom', 'missing-result', 'extra-result')
        with tarfile.open(archive_path) as archive:
            for label in labels:
                name = label + '.tar'
                with archive.extractfile(name) as source:
                    (directory / name).write_bytes(source.read())
        args.reference = directory / 'reference.tar'
        args.solution = directory / 'valid.tar'
        compare(args)
        for label, diagnostic in [('changed-definition', 'does not match'),
                                  ('unused-definition', 'does not match'),
                                  ('forbidden-axiom', 'illegal axiom'),
                                  ('missing-result', 'coverage changed'),
                                  ('extra-result', 'coverage changed')]:
            args.solution = directory / f'{label}.tar'
            # Exercise Comparator's own axiom traversal for the forbidden-axiom
            # case; the positive fixture already exercises both kernels.
            args.kernels = 'lean' if label == 'forbidden-axiom' else 'both'
            result = subprocess.run(comparison_command(args), text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode == 0 or diagnostic not in result.stdout.lower():
                raise ValueError(f'{label}: expected a specific rejection, got {result.returncode}:\n{result.stdout}')
            print(f'PASS: {label} was rejected.', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--image', default='distributed-synthesis-audit', help='Local image-name prefix')
    parser.add_argument('--jobs', type=int, default=2)
    commands = parser.add_subparsers(dest='command', required=True)
    commands.add_parser('fast', help='Run the incremental Lean build and our axiom/boundary checker')
    chk = commands.add_parser('check', help='Prepare Docker, export the checkout, and run Comparator')
    chk.add_argument('--reference', type=Path, required=True, help='Previously reviewed reference bundle')
    chk.add_argument('--project', type=Path, default=ROOT)
    chk.add_argument('--kernels', choices=('lean', 'both'), default='lean')
    ref = commands.add_parser('reference', help='Prepare Docker and save a reviewed reference (never overwrite)')
    ref.add_argument('--project', type=Path, default=ROOT)
    ref.add_argument('--output', type=Path, required=True)
    commands.add_parser('build', help='Build pinned Debian-slim checker and exporter images')
    commands.add_parser('self-test', help='Test acceptance and rejection of changed definitions, axioms, and coverage')
    exp = commands.add_parser('export', help='Compile and export a checkout in an offline container')
    exp.add_argument('--project', type=Path, default=ROOT, help='Lean project root, containing lean-toolchain')
    exp.add_argument('--output', type=Path, required=True, help='New .tar bundle outside the repository')
    cmp = commands.add_parser('compare', help='Compare with a previously reviewed, separately saved reference')
    cmp.add_argument('--reference', type=Path, required=True)
    cmp.add_argument('--solution', type=Path, required=True)
    cmp.add_argument('--kernels', choices=('lean', 'both'), default='lean',
                     help='Comparator/Lean (default), or also require Nanoda; no automatic fallback')
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    try:
        {'fast': fast, 'check': check, 'reference': reference,
         'build': build, 'export': export, 'compare': compare,
         'self-test': self_test}[args.command](args)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f'Audit failed: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
