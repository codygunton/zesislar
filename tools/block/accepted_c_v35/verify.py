"""Check the immutable source transfer without compiling or installing it."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
manifest = json.loads((root / "MANIFEST.json").read_text())
for row in manifest["files"]:
    source = root / row["file"]
    assert source.resolve().is_relative_to(root)
    assert source.suffix in {".v", ".vpart"}
    assert hashlib.sha256(source.read_bytes()).hexdigest() == row["sha256"], source
assert not any(root.rglob("*.vo"))
assert manifest["objects_copied"] is False
print(f"Verified {len(manifest['files'])} source bindings.")
