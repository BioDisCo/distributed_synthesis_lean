#!/usr/bin/env python3
"""Trusted container entry points; never import Python code from the candidate."""
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import tarfile
from checker_lean import checker_lean
from bundles import check_result_modules, matching_coverage, read_bundle, write_bundle

AUDIT = Path('/opt/audit')
LOCKFILES = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')


def run(args, **kwargs):
    return subprocess.run(args, check=True, **kwargs)


def export():
    source, seed, project = Path('/source'), Path('/opt/seed'), Path('/work/project')
    for name in LOCKFILES:
        if (source / name).read_bytes() != (seed / name).read_bytes():
            raise RuntimeError(f'{name} differs from the image; rebuild the image for this toolchain/lockfile')
    project.mkdir()
    for name in (*LOCKFILES, 'DistributedSynthesis.lean'):
        shutil.copyfile(source / name, project / name)
    shutil.copytree(source / 'DistributedSynthesis', project / 'DistributedSynthesis')
    shutil.copytree(seed / '.lake', project / '.lake', symlinks=True)
    # No host .lake cache or project executables are loaded. Build in the offline
    # container; all writable state belongs to its disposable volume.
    config = json.loads((AUDIT / 'targets.json').read_text())
    run(['lake', 'build', config['solution_module']], cwd=project, stdout=sys.stderr)
    manifest, declarations = Path('/work/manifest.json'), Path('/work/declarations.ndjson')
    with declarations.open('wb') as handle:
        run(['lake', 'env', '/opt/exporter/.lake/build/bin/export_project',
             config['solution_module'], str(AUDIT / 'export-targets.json'), str(manifest)],
            cwd=project, stdout=handle)
    check_result_modules(project, json.loads(manifest.read_text()))
    write_bundle(manifest, declarations, sys.stdout.buffer)


def compare():
    kernels = sys.argv[2] if len(sys.argv) > 2 else 'both'
    if kernels not in ('lean', 'both'):
        raise ValueError('Expected kernel mode lean or both')
    reference = read_bundle('/reference.tar', Path('/work/reference.ndjson'))
    solution = read_bundle('/solution.tar', Path('/work/solution.ndjson'))
    matching_coverage(reference, solution)
    config = json.loads((AUDIT / 'targets.json').read_text())
    config['theorem_names'] = reference['theorem_names']
    Path('/work/comparator.json').write_text(json.dumps(config))
    Path('/work/rigid.json').write_text(json.dumps(reference['rigid_names']))
    print(f"Public API coverage: {len(reference['theorem_names'])} theorems and "
          f"{len(reference['rigid_names'])} fixed declarations.", flush=True)
    nanoda = {
        'export_file_path': '/work/solution.ndjson',
        'use_stdin': False,
        'permitted_axioms': config['permitted_axioms'],
        'unpermitted_axiom_hard_error': True,
        'nat_extension': True,
        'string_extension': True,
        # Upstream worker threads have a fixed 16 MiB stack. Some of our proof
        # terms exceed it; serial checking uses the larger process stack below.
        'num_threads': 1,
    }
    config_path = Path('/tmp/nanoda.json')
    config_path.write_text(json.dumps(nanoda))
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (512 * 1024 * 1024, hard))
    if kernels == 'both':
        run(['nanoda_bin', str(config_path)])
        print('Nanoda independent kernel: passed.', flush=True)
    else:
        print('Kernel mode: Lean. Nanoda was not requested.', flush=True)
    checker_lean('CompareExports.lean')
    checked = 'Nanoda and Comparator' if kernels == 'both' else 'Comparator'
    print(f'PASS: {checked} accepted the supplied comparison.', flush=True)


def fixtures():
    """Small genuine Lean exports exercising acceptance and two rejection paths."""
    lean = '/opt/elan/toolchains/leanprover--lean4---v4.30.0/bin/lean'
    exporter = '/opt/exporter/.lake/build/bin/export_project'
    files = []
    for label in ('reference', 'valid', 'changed-definition', 'unused-definition',
                  'forbidden-axiom', 'missing-result', 'extra-result'):
        directory = Path('/work') / label
        (directory / 'DistributedSynthesis').mkdir(parents=True)
        proposition = 'False' if label == 'changed-definition' else 'True'
        source = f'def auditStatement : Prop := {proposition}\n'
        source += f'def unusedDefinition : Nat := {2 if label == "unused-definition" else 1}\n'
        forbidden = label == 'forbidden-axiom'
        if forbidden:
            source += 'private axiom auditForbidden : auditStatement → auditStatement\n'
        proof = 'auditForbidden' if forbidden else '(fun h => h)'
        names = ['firstResult', 'secondResult']
        if label == 'missing-result':
            names.pop()
        if label == 'extra-result':
            names.append('newResult')
        for name in names:
            source += f'theorem {name} : auditStatement → auditStatement := {proof}\n'
        module = 'DistributedSynthesis.Results'
        path = 'DistributedSynthesis/Results'
        (directory / (path + '.lean')).write_text(source)
        run([lean, '-o', path + '.olean', path + '.lean'], cwd=directory, stdout=sys.stderr)
        env = os.environ.copy()
        env['LEAN_PATH'] = str(directory)
        declarations = directory / 'declarations.ndjson'
        manifest = directory / 'manifest.json'
        with declarations.open('wb') as handle:
            run([exporter, module, str(AUDIT / 'export-targets.json'), str(manifest)],
                env=env, stdout=handle)
        output = directory / f'{label}.tar'
        with output.open('wb') as handle:
            write_bundle(manifest, declarations, handle)
        files.append(output)
    with tarfile.open(fileobj=sys.stdout.buffer, mode='w|') as archive:
        for path in files:
            archive.add(path, arcname=path.name)


if __name__ == '__main__':
    try:
        {'export': export, 'compare': compare, 'fixtures': fixtures}[sys.argv[1]]()
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        detail = str(error)
        if len(detail) > 3000:
            detail = detail[:3000] + ' ... (additional diagnostics omitted)'
        print(f'Verification failed: {detail}', file=sys.stderr)
        sys.exit(1)
