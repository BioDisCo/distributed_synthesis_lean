#!/usr/bin/env python3
"""Check the paper guide's source links, entry coverage, and axiom-audit coverage."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
ENTRIES = ROOT / 'DistributedSynthesis/Formalizations/Paper'
DECLARATION = re.compile(r'^(theorem|def|abbrev)\s+(\w+)', re.MULTILINE)
LINK = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')


def link_errors(document):
    """Reject missing files, stale line numbers, and mismatched declaration names."""
    errors = []
    for label, url in LINK.findall(document.read_text()):
        if '://' in url or url.startswith('#'):
            continue
        path, _, fragment = url.partition('#')
        target = document.parent / path
        if not target.is_file():
            errors.append(f'{document.name}: missing file {url}')
            continue
        if not fragment:
            continue
        text = target.read_text()
        if fragment.startswith('L') and fragment[1:].isdigit():
            lines = text.splitlines()
            line = int(fragment[1:])
            if not 1 <= line <= len(lines):
                errors.append(f'{document.name}: invalid line {url}')
                continue
            if label.startswith('`') and label.endswith('`'):
                name = re.escape(label[1:-1].split('.')[-1])
                if not re.search(r'\b(?:theorem|lemma|def|abbrev|namespace)\s+' + name + r'\b', lines[line - 1]):
                    errors.append(f'{document.name}: {label} is not at {url}')
        elif target.suffix == '.md':
            headings = re.findall(r'^#+ (.+)$', text, re.MULTILINE)
            anchors = {re.sub(r'[^a-z0-9 -]', '', h.lower()).replace(' ', '-') for h in headings}
            if fragment not in anchors:
                errors.append(f'{document.name}: missing heading {url}')
        else:
            errors.append(f'{document.name}: unsupported fragment {url}')
    return errors


def main():
    errors = []
    guides = [ENTRIES / 'README.md', ENTRIES / 'PROOFS.md']
    for guide in guides:
        errors.extend(link_errors(guide))
    index, proofs = (p.read_text() for p in guides)
    audited = set(re.findall(r'^#print axioms (\S+)',
        (ROOT / 'DistributedSynthesis/Tests/Paper/Audit.lean').read_text(), re.MULTILINE))
    imports = set(re.findall(r'^import (\S+)',
        (ROOT / 'DistributedSynthesis/Tests/Paper.lean').read_text(), re.MULTILINE))
    declarations = theorem_count = 0
    entries = sorted(ENTRIES.glob('*.lean'))
    for entry in entries:
        if f']({entry.name})' not in index:
            errors.append(f'{entry.name}: missing from the paper guide')
        module = f'DistributedSynthesis.Formalizations.Paper.{entry.stem}'
        if module not in imports:
            errors.append(f'{entry.name}: not imported by Tests.Paper')
        source = entry.read_text()
        for match in DECLARATION.finditer(source):
            kind, name = match.groups()
            declarations += 1
            line = source.count('\n', 0, match.start()) + 1
            if f'[`{name}`]({entry.name}#L{line})' not in proofs:
                errors.append(f'{entry.name}: missing or stale proof-guide entry for {name}')
            if kind == 'theorem':
                theorem_count += 1
                if f'DistributedSynthesis.Paper.{entry.stem}.{name}' not in audited:
                    errors.append(f'{entry.name}: {name} is missing from the axiom audit')
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        return 1
    print(f'Paper guide passed: {len(entries)} entry files, {declarations} declarations, '
          f'{theorem_count} audited theorems; source links and line anchors checked.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
