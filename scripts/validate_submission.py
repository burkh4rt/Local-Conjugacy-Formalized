#!/usr/bin/env python3
"""Check this project's Palomar metadata/configuration and exact result inventory.

This deliberately complements, rather than claims to be, Palomar's verifier.
The trusted registry controls dependency authentication and remote verification.
"""

import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
metadata = json.loads(
    subprocess.check_output(
        [
            "ruby",
            "-ryaml",
            "-rjson",
            "-e",
            "puts JSON.generate(YAML.safe_load(File.read(ARGV[0]), aliases: false))",
            str(root / "formalization.yaml"),
        ],
        text=True,
    )
)


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def text(value):
    return isinstance(value, str) and bool(value.strip())


def person(value):
    # Palomar accepts name strings and person mappings with a separate ORCID field.
    return text(value) or (isinstance(value, dict) and text(value.get("name")))


require(metadata.get("version") == "v0.4", "Metadata version must be v0.4")
project = metadata["project"]
for key, limit in [("name", 300), ("description", 10000)]:
    require(
        text(project.get(key)) and len(project[key]) <= limit, f"Invalid project.{key}"
    )
for key in ["authors", "responsible_maintainers"]:
    require(
        isinstance(project.get(key), list)
        and project[key]
        and all(map(person, project[key])),
        f"Invalid project.{key}",
    )
require(
    project["license"] == "Apache-2.0",
    "License must agree with inherited Apache-2.0 LICENSE",
)
require(
    (root / "LICENSE").read_text().lstrip().startswith("Apache License"),
    "Unexpected license file",
)
require(
    "repository" not in metadata,
    "This is the substantive development, not a thin wrapper",
)
require(
    metadata["classification"]["arxiv"] == ["math.GR"],
    "Unexpected arXiv classification",
)
require(
    set(metadata["classification"]["msc2020"]) == {"20E18", "20E45", "20J06", "05E18"},
    "MSC codes must match the preprint",
)
sources = metadata.get("sources")
require(isinstance(sources, list) and sources, "Sources must be nonempty")
for source in sources:
    require(text(source.get("title")), "A source has no title")
    require(
        source.get("relationship")
        in {"formalizes", "adapts", "independently-proves", "background", "other"},
        "Invalid source relationship",
    )
    require(
        source.get("type")
        in {
            None,
            "paper",
            "book",
            "web discussion",
            "folklore",
            "original-proof",
            "other",
        },
        "Invalid Palomar source type",
    )
require(
    any(
        s.get("id") == "arXiv:2609.37678v1" and s["relationship"] == "formalizes"
        for s in sources
    ),
    "The versioned preprint must be the formalized source",
)
require(
    all(s.get("type") != "original-proof" for s in sources),
    "This is source-based mathematics",
)
methods = metadata["automation"]["methods"]
require(
    methods and all(text(m.get("method")) for m in methods),
    "Missing automation disclosure",
)
require(text(metadata["review"].get("status")), "Missing review status")
require(
    (root / "formalization.yaml").stat().st_size <= 256 * 1024,
    "Metadata exceeds size limit",
)

config = json.loads((root / "comparator.json").read_text())
require(
    set(config)
    <= {
        "challenge_module",
        "solution_module",
        "theorem_names",
        "definition_names",
        "permitted_axioms",
        "enable_nanoda",
    },
    "Unaccepted Comparator configuration field",
)
require(
    config["challenge_module"] == "Challenge"
    and config["solution_module"] == "Solution",
    "Unexpected Challenge/Solution module names",
)
require(
    config.get("definition_names", []) == [], "This submission has no definition holes"
)
require(
    set(config["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"},
    "Only the three standard axioms are permitted",
)
inv = json.loads((root / "reports/source-result-inventory.json").read_text())
source_hash = hashlib.sha256(
    (root / "sources/local-conjugacy-prosolvable-re.tex").read_bytes()
).hexdigest()
require(
    source_hash == inv["source_sha256"],
    "Source inventory no longer matches the preprint",
)
expected = [r["lean"] for r in inv["results"] + inv["counterexamples"]]
require(
    len(expected) == 13
    and len(config["theorem_names"]) == 13
    and set(config["theorem_names"]) == set(expected),
    "Comparator does not cover all thirteen source results",
)
require(
    set(s["lean"] for s in metadata["alignment"]["statements"]) == set(expected),
    "Metadata alignment differs from the compared declarations",
)
require(metadata["alignment"]["namespace"] == "LocalConjugacy", "Wrong namespace")
require(
    all(n.startswith("LocalConjugacy.") for n in expected),
    "A theorem lies outside LocalConjugacy",
)
manifest = json.loads((root / "lake-manifest.json").read_text())
for dep in manifest["packages"]:
    require(
        dep["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", dep["rev"]),
        f"Dependency {dep['name']} is not pinned to a Git commit",
    )
print(
    "Metadata, pinned dependencies, Comparator configuration, and thirteen-result arXiv inventory agree."
)
