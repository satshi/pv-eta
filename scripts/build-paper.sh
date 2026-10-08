#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../paper"
if ! command -v pdflatex >/dev/null 2>&1; then
  printf '%s\n' 'pdflatex was not found. Install TeX Live or MacTeX and the packages listed in README.md.' >&2
  exit 1
fi
mkdir -p build
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
    -output-directory=build pv_eta_invariant_en.tex
done
printf '%s\n' 'Built paper/build/pv_eta_invariant_en.pdf'
