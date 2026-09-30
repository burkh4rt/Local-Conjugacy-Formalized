#!/usr/bin/env python3
"""Check compiled declarations and axioms; fail on missing requested proofs.

--allow-incomplete permits the development subset, but still fails if any
implemented result has a mismatched statement or a disallowed axiom.
"""

from pathlib import Path
import datetime
import hashlib
import json
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
run = subprocess.run(
    ["lake", "env", "lean", "--run", "scripts/Audit.lean"],
    cwd=root,
    text=True,
    capture_output=True,
)
if run.returncode:
    print(run.stdout + run.stderr)
    raise SystemExit(run.returncode)
rows = [json.loads(line) for line in run.stdout.splitlines() if line.startswith("{")]
results = [r for r in rows if "name" in r]
support = [r for r in rows if "supporting_theorem" in r]
definitions = [r for r in rows if "definition" in r]
shared = [r for r in rows if "shared_theorem" in r]
shared_mismatches = [r for r in shared if not r["same_proof"]]
expected = json.loads((root / "comparator.json").read_text())["theorem_names"]
if {r["name"] for r in results} != set(expected):
    raise SystemExit("Audit.lean and comparator.json target lists differ")
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = [r for r in rows if set(r.get("axioms", [])) - allowed]
definition_mismatches = [r for r in definitions if not r["same_definition"]]
mismatches = [r for r in results if r["solution_present"] and not r["same_type"]]
missing = [r["name"] for r in results if not r["solution_present"]]
absent_challenge = [r["name"] for r in results if not r["challenge_present"]]
source_paths = sorted(
    [
        *root.glob("LocalConjugacy/**/*.lean"),
        root / "LocalConjugacy.lean",
        root / "Solution.lean",
    ]
)
source_hashes = {
    str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
    for p in source_paths
}
manifest = json.loads((root / "lake-manifest.json").read_text())
report = {
    "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "check": "Compiled structural type comparison and transitive axiom audit; check.sh builds first",
    "toolchain": (root / "lean-toolchain").read_text().strip(),
    "mathlib_revision": next(
        p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"
    ),
    "challenge_sha256": hashlib.sha256(
        (root / "Challenge.lean").read_bytes()
    ).hexdigest(),
    "manuscript_sha256": hashlib.sha256(
        (root / "sources/local-conjugacy-prosolvable-re.tex").read_bytes()
    ).hexdigest(),
    "solution_source_hashes": source_hashes,
    "full_comparator_run": False,
    "nanoda_run": False,
    "con_ron_run": False,
    "submission_ready": False,
    "missing_solution_declarations": missing,
    "missing_challenge_declarations": absent_challenge,
    "type_mismatches": mismatches,
    "disallowed_axioms": bad,
    "definitions_compared": len(definitions),
    "definition_mismatches": definition_mismatches,
    "shared_helper_proofs_compared": len(shared),
    "shared_helper_mismatches": shared_mismatches,
    "results": results,
    "supporting_theorems_audited": len(support),
    "supporting_theorems": support,
}
(root / "reports").mkdir(exist_ok=True)
(root / "reports/validation.json").write_text(json.dumps(report, indent=2) + "\n")
print(
    f"{len(results) - len(missing)}/{len(results)} requested declarations implemented; "
    f"{len(support)} supporting theorem declarations audited."
)
for name in missing:
    print("MISSING:", name)
if bad or mismatches or absent_challenge or definition_mismatches or shared_mismatches:
    print(
        "FAILED: axiom, statement-type, or Challenge checks; see reports/validation.json"
    )
    raise SystemExit(1)
print(
    "Implemented declarations use only permitted axioms and match their Challenge types."
)
if missing and "--allow-incomplete" not in sys.argv:
    print("NOT READY FOR SUBMISSION: requested proofs remain missing.")
    raise SystemExit(1)
if missing:
    print("Development subset passed. The complete submission remains blocked.")
