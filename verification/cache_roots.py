"""Fetch only the Mathlib import closure needed by the source recipe."""
from pathlib import Path
import re
import subprocess

roots = set()
for path in Path('DistributedSynthesis').rglob('*.lean'):
    roots.update(re.findall(r'^import (Mathlib\.[\w.]+)', path.read_text(), re.M))
if not roots:
    raise RuntimeError('No Mathlib imports found')
subprocess.run(['lake', 'exe', 'cache', 'get', *sorted(roots)], check=True)
