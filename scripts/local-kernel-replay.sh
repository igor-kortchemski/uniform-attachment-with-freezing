#!/bin/sh
# LOCAL diagnostic only; not the official Palomar verification.
# Usage: scripts/local-kernel-replay.sh CONFIG.json SOLUTION.ndjson OUT
set -eu
exec python3 "$(dirname "$0")/verification.py" replay "$@"
