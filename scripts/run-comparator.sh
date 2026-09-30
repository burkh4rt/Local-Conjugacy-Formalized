#!/usr/bin/env bash
# Follow Palomar's toolchain-bundled Comparator workflow. See SUBMIT.md.
set -euo pipefail
cd "$(dirname "$0")/.."
bash scripts/check.sh
if [ "$(uname -s)" != Linux ]; then
	echo 'Sandboxed Comparator requires Linux with Bubblewrap; the local audit above is separate.' >&2
	exit 2
fi
for required_command in bwrap lake lean python3; do
	if ! command -v "$required_command" >/dev/null 2>&1; then
		echo "Missing command: $required_command" >&2
		exit 2
	fi
done
toolchain_prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
	if [ ! -x "$toolchain_prefix/bin/$tool" ]; then
		echo "The pinned toolchain does not bundle $tool." >&2
		exit 2
	fi
done
comparator_config=$(mktemp "${TMPDIR:-/tmp}/lcp-comparator.XXXXXX")
trap 'rm -f "$comparator_config"' EXIT
python3 - comparator.json "$comparator_config" "$toolchain_prefix" <<'PY'
import json
from pathlib import Path
import sys
source, destination, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text())
if 'external_kernels' in config:
    raise SystemExit('external_kernels is not permitted in the submitted comparator.json')
config.pop('enable_nanoda', None)
config['external_kernels'] = {
    'nanoda': [f'{prefix}/bin/nanoda_bin'],
    'con-ron': [f'{prefix}/bin/con-ron'],
}
Path(destination).write_text(json.dumps(config, indent=2) + '\n')
PY
lake comparator --config "$comparator_config" 2>&1 | tee reports/comparator.log
python3 - <<'PY'
import datetime
import hashlib
import json
from pathlib import Path
audit = json.loads(Path('reports/validation.json').read_text())
report = {
    'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'toolchain': Path('lean-toolchain').read_text().strip(),
    'sandboxed_comparator': 'passed',
    'kernels': ['Lean', 'nanoda', 'con-ron'],
    'mathlib_revision': audit['mathlib_revision'],
    'challenge_sha256': audit['challenge_sha256'],
    'solution_source_hashes': audit['solution_source_hashes'],
    'manifest_sha256': hashlib.sha256(Path('lake-manifest.json').read_bytes()).hexdigest(),
    'configuration_sha256': hashlib.sha256(Path('comparator.json').read_bytes()).hexdigest(),
    'human_statement_review': 'record separately in formalization.yaml',
}
Path('reports/comparator-validation.json').write_text(json.dumps(report, indent=2) + '\n')
PY
