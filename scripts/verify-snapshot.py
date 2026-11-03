"""Verify exported proof modules against the independently checked upstream snapshot."""
import hashlib
import json
from pathlib import Path
root = Path(__file__).resolve().parent.parent
manifest = json.loads((root / 'provenance/upstream-lean-snapshot.json').read_text())
changed = [name for name, digest in manifest['files'].items()
           if not (root / name).is_file()
           or hashlib.sha256((root / name).read_bytes()).hexdigest() != digest]
if changed:
    raise SystemExit('Upstream proof snapshot differs: ' + ', '.join(changed))
print(f"Verified {len(manifest['files'])} original proof modules against upstream snapshot.")
