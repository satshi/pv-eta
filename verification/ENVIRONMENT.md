# Local verification record

Verification date: 2026-10-08.

- Lean: 4.19.0, official Linux x86-64 release, commit `6caaee842e94`.
- mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Project build: `lake build PVEta`.
- Logical dependency audit: `lake env lean -DwarningAsError=true PVEta/Audit.lean`.
- Reproduction entry point: `./scripts/check.sh`.

`build.txt` and `audit.txt` contain the successful local command output. The
axiom audit examines every kernel-safe declaration under `PVEta`, including
auxiliary logical declarations. Lean's unsafe compiler IR helpers are excluded:
they are not logical constants usable in safe proofs. The principal theorems'
axiom lists are also printed individually. Local theorem hypotheses are not
axioms and remain visible in the source and README.

This is a local Lean check, not a recorded GitHub Actions run or an independent
second-kernel verification. The supplied workflow reproduces the ordinary Lean
build and the same dependency audit on a standard GitHub runner.

## Authoring-runtime compatibility

The authoring environment exposed `/proc/self/exe` but not `/proc/<pid>/exe`.
The official Lean 4.19 binaries consequently failed to locate their own
installation. A small local `LD_PRELOAD` wrapper redirected only `readlink`
queries for the current process's own `/proc/<pid>/exe` to `/proc/self/exe`.
Its full source is `runtime-proc-self.c` in this directory.

This wrapper did not alter the Lean executable, theorem statements, proof terms,
or kernel routines. It was an environment compatibility measure and is not
used by `scripts/check.sh` or by the GitHub workflow. Ordinary Linux installations
do not need it. The local build used the wrapper through the invoking process's
environment; the project files contain no dependency on that local path.

## Combined source distribution

The repository packaging was updated on 2026-10-08 to include the English
manuscript in `paper/`, a paper build script, and the expanded README and Git
ignore rules. The Lean source files, toolchain, dependency manifest, and Lean
verification script are unchanged from the checked version recorded above.
`SHA256SUMS` records the files in this combined distribution. The bundled paper
source and PDF were copied unchanged from the existing manuscript artifacts.
