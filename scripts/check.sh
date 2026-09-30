#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/generate_challenge.py --check
python3 scripts/check_source_layout.py
lake build
ruby scripts/validate-formalization.rb
python3 scripts/validate_submission.py
python3 scripts/check_status.py "$@"
