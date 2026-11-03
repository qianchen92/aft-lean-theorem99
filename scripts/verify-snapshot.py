"""Check source integrity and the exact dependency closure of the root theorem."""
import hashlib
import json
import os
import re
from pathlib import Path

root = Path(__file__).resolve().parent.parent
manifest = json.loads((root / 'provenance/upstream-lean-snapshot.json').read_text())
pruned = json.loads((root / 'provenance/pruned-modules.json').read_text())
original = manifest['files']
removed = pruned['files']
for name, digest in removed.items():
    if original.get(name) != digest:
        raise SystemExit('Pruning record is not in upstream snapshot: ' + name)
    if (root / name).exists():
        raise SystemExit('Pruned module has reappeared: ' + name)
retained = {name: digest for name, digest in original.items() if name not in removed}
changed = [name for name, digest in retained.items()
           if not (root / name).is_file()
           or hashlib.sha256((root / name).read_bytes()).hexdigest() != digest]
if changed:
    raise SystemExit('Upstream proof snapshot differs: ' + ', '.join(changed))

modules = {}
for directory, dirs, files in os.walk(root):
    dirs[:] = [name for name in dirs if name not in {'.git', '.lake'}]
    for name in files:
        if name.endswith('.lean'):
            path = Path(directory) / name
            module = '.'.join(path.relative_to(root).with_suffix('').parts)
            modules[module] = path

reached = set()
def visit(module):
    if module in reached:
        return
    if module not in modules:
        if module.split('.')[0] in {'AFT', 'CurrentAFT', 'Theorem99', 'Audit'}:
            raise SystemExit('Missing local import: ' + module)
        return  # Lean/mathlib dependencies are checked by Lake and the lockfile.
    reached.add(module)
    for line in modules[module].read_text().splitlines():
        match = re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(.+)', line)
        if match:
            for imported in match.group(1).split('--', 1)[0].split():
                visit(imported)
for module in ['Theorem99', 'Audit']:
    visit(module)
unused = sorted(set(modules) - reached)
if unused:
    raise SystemExit('Unused local Lean modules: ' + ', '.join(unused))
expected = set(retained) | {'Theorem99.lean', 'Audit.lean'}
actual = {str(path.relative_to(root)) for path in modules.values()}
if actual != expected:
    raise SystemExit('Unexpected source inventory: ' + str(sorted(actual ^ expected)))
print(f'Verified {len(retained)} unchanged upstream modules; '
      f'{len(removed)} explicitly pruned; all {len(reached)} shipped Lean modules are reachable.')
