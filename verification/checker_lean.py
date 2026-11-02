"""Launch a trusted Lean adapter with Comparator's Main first on the path."""
import os
from pathlib import Path
import subprocess
import sys


def checker_lean(filename):
    # Resolve Lake dependencies while building the trusted image. At runtime
    # the filesystem is read-only and no package manager needs to execute.
    paths = Path('/opt/audit/lean-path').read_text().strip()
    env = os.environ.copy()
    env['LEAN_PATH'] = '/opt/comparator/.lake/build/lib/lean:' + paths
    lean = '/opt/elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean'
    subprocess.run([lean, '/opt/audit/' + filename], env=env, check=True)


if __name__ == '__main__':
    checker_lean(sys.argv[1])
