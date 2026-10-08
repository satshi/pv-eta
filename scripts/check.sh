#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
lake build
lake env lean -DwarningAsError=true PVEta/Audit.lean
