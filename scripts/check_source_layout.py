#!/usr/bin/env python3
"""Check this submission's module headers, source limits, and pinned source.

The Lean build checks header syntax. This check enforces the repository's
convention that `module` is the first line and scans unused Lean files too.
"""

from pathlib import Path
import hashlib
import json
import os

root = Path(__file__).resolve().parents[1]
files = []
for directory, subdirs, names in os.walk(root, followlinks=False):
    subdirs[:] = [name for name in subdirs if name not in {".git", ".lake"}]
    for name in names:
        if name.endswith(".lean"):
            path = Path(directory) / name
            if path.is_symlink():
                raise SystemExit(
                    f"Lean symbolic link is not permitted: {path.relative_to(root)}"
                )
            text = path.read_text(encoding="utf-8")
            lines = text.splitlines()
            if len(lines) > 10_000:
                raise SystemExit(
                    f"Source exceeds 10,000 lines: {path.relative_to(root)}"
                )
            if name != "lakefile.lean" and (not lines or lines[0] != "module"):
                raise SystemExit(f"Expected module header: {path.relative_to(root)}")
            files.append({"file": str(path.relative_to(root)), "lines": len(lines)})

fingerprints = json.loads((root / "reports/source-fingerprints.json").read_text())
for key in ["manuscript", "arxiv_archive"]:
    source = fingerprints[key]
    actual = hashlib.sha256((root / source["path"]).read_bytes()).hexdigest()
    if actual != source["sha256"]:
        raise SystemExit(f"{key} differs from the reviewed source fingerprint")

manifest = json.loads((root / "lake-manifest.json").read_text())
mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
toolchain = (root / "lean-toolchain").read_text().strip()
mathlib_toolchain = root / ".lake/packages/mathlib/lean-toolchain"
if mathlib_toolchain.exists() and mathlib_toolchain.read_text().strip() != toolchain:
    raise SystemExit("The project toolchain differs from the pinned Mathlib toolchain")

report = {
    "files": sorted(files, key=lambda f: f["file"]),
    "source_fingerprints_match": True,
    "toolchain": toolchain,
    "mathlib_revision": mathlib["rev"],
    "largest_source_lines": max(f["lines"] for f in files),
}
(root / "reports/source-layout.json").write_text(json.dumps(report, indent=2) + "\n")
print(
    f"{len(files)} Lean sources use module headers; largest has "
    f"{report['largest_source_lines']} lines. Source fingerprints match."
)
