#!/usr/bin/env bash
# For this trusted local development on macOS. This is NOT a sandboxed run.
# Palomar's official verification must still be run in its trusted environment.
set -euo pipefail
cd "$(dirname "$0")/.."
bash scripts/check.sh
prefix=$(lean --print-prefix)
config=$(mktemp "${TMPDIR:-/tmp}/local-conjugacy-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
from pathlib import Path
import sys
source, destination, prefix = sys.argv[1:]
c = json.loads(Path(source).read_text())
c['external_kernels'] = {'nanoda': [prefix + '/bin/nanoda_bin'],
                         'con-ron': [prefix + '/bin/con-ron']}
Path(destination).write_text(json.dumps(c, indent=2) + '\n')
PY
lake comparator --inadvisably-no-sandbox --config "$config" 2>&1 | tee reports/local-comparator.log
python3 - <<'PY'
import datetime
import hashlib
import json
from pathlib import Path
r = json.loads(Path('reports/validation.json').read_text())
report = {
    'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'comparator': 'passed', 'sandboxed': False,
    'invocation': 'lake comparator --inadvisably-no-sandbox; temporary configuration adds nanoda and con-ron',
    'kernels': ['Lean', 'nanoda', 'con-ron'],
    'toolchain': r['toolchain'], 'mathlib_revision': r['mathlib_revision'],
    'challenge_sha256': r['challenge_sha256'],
    'solution_source_hashes': r['solution_source_hashes'],
    'configuration_sha256': hashlib.sha256(Path('comparator.json').read_bytes()).hexdigest(),
    'official_palomar_verification': False,
}
Path('reports/local-comparator-validation.json').write_text(json.dumps(report, indent=2) + '\n')
PY
