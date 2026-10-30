#!/bin/sh
# Official sandboxed Linux Comparator checks; no dispatch or publication.
# Usage: scripts/run-linux-checks.sh OUT
set -eu
exec python3 "$(dirname "$0")/verification.py" linux "$@"
