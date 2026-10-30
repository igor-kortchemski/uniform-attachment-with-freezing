#!/bin/sh
# LOCAL diagnostic only; not the official Palomar verification.
# Usage: scripts/local-comparator-diagnostic.sh CONFIG.json OUT
set -eu
exec python3 "$(dirname "$0")/verification.py" compare "$@"
