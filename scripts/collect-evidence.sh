#!/bin/sh
# LOCAL diagnostic only; not the official Palomar verification.
# Usage: scripts/collect-evidence.sh OUT [ROOT]
set -eu
exec python3 "$(dirname "$0")/verification.py" collect "$@"
