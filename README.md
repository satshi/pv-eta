# Pauli–Villars phases and the eta invariant

The English manuscript *Finite Pauli–Villars Products and the Eta Invariant*,
together with a Lean 4 formalization of its analytic phase-convergence argument.

- [Read the paper (PDF)](paper/pv_eta_invariant_en.pdf).
- [Edit the paper (LaTeX)](paper/pv_eta_invariant_en.tex).
- [Read the main formal theorem](PVEta/Product.lean).

The formal result relates a **normalized, eigenvalue-wise grouped
Pauli–Villars product** to a heat-defined eta invariant.

The code proves the scalar arctangent identity, the regulator-kernel estimates,
the exchange of a spectral sum with an integral, convergence of the real phase
lift, and convergence of the corresponding infinite product. It is a companion
to the expository manuscript *Finite Pauli–Villars Products and the Eta Invariant*.
It is not a claim of a new geometric eta-invariant theorem.

**Scope:** the formal theorem assumes explicitly stated spectral summability and
absolute-integrability hypotheses. It does **not** formalize the construction of
a Dirac operator, Weyl's law, the Bismut–Freed heat-kernel estimate, or the
identification of the heat integral with the meromorphic spectral eta function.
In particular, do not describe this repository as a complete formalization of
Witten's fermion partition-function construction.

## Repository layout

| Path | Contents |
| --- | --- |
| `paper/pv_eta_invariant_en.tex` | Self-contained English manuscript, with its bibliography |
| `paper/pv_eta_invariant_en.pdf` | Precompiled manuscript, intentionally tracked in Git |
| `PVEta/` | Lean definitions, lemmas, main theorems, and axiom audit |
| `PVEta.lean` | Entry point importing the formalization |
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | Pinned Lean and dependency configuration |
| `scripts/check.sh` | Lean build and axiom-dependency checks |
| `scripts/build-paper.sh` | Two-pass pdfLaTeX build |
| `.github/workflows/lean.yml` | GitHub Actions workflow for Lean verification |
| `verification/` | Recorded verification output and source-file checksums |
| `.gitignore`, `.gitattributes` | Generated-file exclusions and text-file settings |

Run commands below from the repository root. The Lean files remain at the root
so Lake and the Lean editor extension recognize the project immediately.
`paper/build/` and `.lake/` are created locally and excluded from Git and this
source distribution. LaTeX intermediate files are also ignored; the supplied
paper PDF is not ignored.

## Build the paper

The PDF is included, so compilation is optional. To rebuild it, install
pdfLaTeX and the packages used in the source: Latin Modern, the AMS packages,
mathtools, geometry, microtype, booktabs, fancyhdr, xcolor, hyperref, and bookmark.
A standard TeX Live or MacTeX installation with these packages is sufficient.
No external bibliography database, figures, BibTeX, or shell escape is needed.

```sh
./scripts/build-paper.sh
```

The result is `paper/build/pv_eta_invariant_en.pdf`. The script keeps the
versioned PDF in `paper/` intact. After reviewing a rebuilt PDF, update the
versioned copy when preparing a new revision:

```sh
cp paper/build/pv_eta_invariant_en.pdf paper/pv_eta_invariant_en.pdf
```

The manuscript's author field is currently empty; fill it in before publication.
The manuscript presents the ordinary mathematical argument. The narrower Lean
verification boundary is documented below.

## Build and check the Lean formalization

Install [elan](https://lean-lang.org/install/) and Git, then run from the
repository root:

```sh
lake exe cache get
lake build
./scripts/check.sh
```

The initial cache download can be substantial. Subsequent builds are incremental.
No Python, LaTeX, or GPU is needed to check the proofs.

The project pins:

- Lean **4.19.0**, through `lean-toolchain`;
- mathlib commit **`c44e0c8ee63ca166450922a373c7409c5d26b00b`** (tag `v4.19.0`);
- transitive dependencies through `lake-manifest.json`.

Commit the manifest. Do not run `lake update` merely to reproduce the recorded
build: dependency updates should be deliberate and separately checked.

## Main statement

Let the nonzero real eigenvalues, counted with their **full complex
multiplicity**, be a sequence `λ : ℕ → ℝ`. Write

$$
T(t)=\sum_k\lambda_k e^{-t\lambda_k^2},\qquad
A(t)=\sum_k|\lambda_k|e^{-t\lambda_k^2},\qquad t>0.
$$

A `Regulator` consists of finitely many positive scales $b_j$ and real weights
$c_j$ with $\sum_jc_j=-1$. The physical weight $+1$ at mass zero is omitted from
this list. Define

$$
H_M(t)=\sum_jc_j\int_0^{b_jM}e^{-tu^2}\,du,\qquad
\theta_M(x)=\sum_jc_j\arctan\frac{b_jM}{x}.
$$

`SpectralHypotheses λ R.kernel` requires:

1. $\lambda_k\ne0$ for every $k$;
2. $\sum_k|\lambda_k|e^{-t\lambda_k^2}<\infty$ for every $t>0$;
3. $\int_0^\infty|H_M(t)|A(t)\,dt<\infty$ for **every $M>0$**;
4. $\int_0^\infty t^{-1/2}|T(t)|\,dt<\infty$.

These are hypotheses in the theorem's type, not hidden global axioms. In
particular, condition 3 is the **grouped** absolute majorant; the individual
regulator terms need not be summable over the spectrum.

Define the real number

$$
\eta_{\mathrm{heat}}=
\frac1{\sqrt\pi}\int_0^\infty t^{-1/2}T(t)\,dt.
$$

The code proves absolute summability of $\sum_k\theta_M(\lambda_k)$ and

$$
\Theta_M:=\sum_k\theta_M(\lambda_k)
=\int_0^\infty H_M(t)T(t)\,dt,
\qquad
\lim_{M\to+\infty}\Theta_M=-\frac\pi2\eta_{\mathrm{heat}}.
$$

The limit is along **real masses**, not merely along an integer subsequence.
For integer weights, put

$$
g_M(x)=\prod_j\left(1+i\frac{b_jM}{x}\right)^{c_j}.
$$

The main product theorem is

$$
\lim_{M\to+\infty}\prod_k\frac{g_M(\lambda_k)}{|g_M(\lambda_k)|}
=\exp\!\left(-\frac{i\pi}{2}\eta_{\mathrm{heat}}\right).
$$

Search for **`PVEta.Regulator.tendsto_normalized_product`** in
[`PVEta/Product.lean`](PVEta/Product.lean). The finite-mass product exists in
Lean's order-independent `HasProd` sense. The theorem does not assert convergence
of the *unnormalized* determinant or its modulus.

## What the proof actually checks

| Component | Formal status | Main declarations |
| --- | --- | --- |
| Scalar Laplace–arctangent identity, including either sign of the eigenvalue | Proved using Fubini and the fundamental theorem of calculus | `scalar_arctan_identity` |
| Gaussian kernel bound and large-mass limit | Proved for the concrete kernel | `Regulator.kernel_bound`, `Regulator.tendsto_kernel` |
| Exchange of the spectral sum and heat integral | Proved from conditions 2–3 | `Regulator.hasSum_angle` |
| Absolute convergence of the arctangent series | Proved | `Regulator.summable_abs_angle` |
| Limit of the real phase lift | Proved from conditions 1–4 | `Regulator.tendsto_phaseLift` |
| Identification with normalized complex PV factors | Proved | `normalize_groupedFactor` |
| Infinite product and its eta-phase limit | Proved | `Regulator.hasProd_normalized`, `Regulator.tendsto_normalized_product` |
| Binomial weights sum to zero, including the physical weight | Proved for every positive regulator order | `coefficient_sum` |
| First three nonconstant moments for the order-four regulator | Proved | `orderFour_moments` |
| Half-lift limit and its square | Proved algebraically/analytically | `Regulator.tendsto_halfPhase`, `unitPhase_half_sq` |
| Weyl estimates imply conditions 2–3 | **Not formalized** | External spectral analysis |
| Bismut–Freed estimate implies condition 4 | **Not formalized** | External geometric analysis |
| Heat eta equals analytically continued spectral eta at zero | **Not formalized** | External Mellin-transform argument |
| Pfaffians, determinant lines, boundaries, and zero-mode factors | **Not formalized** | External geometry |

The limit of $H_M$ and its uniform bound are conclusions, not assumptions:

$$
H_M(t)\longrightarrow-\frac{\sqrt\pi}{2\sqrt t},\qquad
|H_M(t)|\le\left(\sum_j|c_j|\right)\frac{\sqrt\pi}{2\sqrt t}.
$$

Thus the theorem does more than apply dominated convergence to a limit supplied
as an axiom. Conversely, the explicit input assumptions still require proof for
any intended Dirac operator.

## Relation to the geometric paper

For an invertible geometric Dirac operator on a closed odd-dimensional manifold,
the usual route to the hypotheses is:

- the Weyl estimate gives heat-trace summability;
- cancellation of sufficiently many binomial moments gives the small-time
  bound for the grouped absolute majorant in condition 3;
- the Bismut–Freed estimate supplies the integrability in condition 4;
- the Mellin representation identifies $\eta_{\mathrm{heat}}$ with $\eta_D(0)$.

These steps are discussed in the [manuscript](paper/pv_eta_invariant_en.pdf) and the references below; this
repository leaves them outside the Lean boundary. No geometric theorem is
silently imported through a custom `axiom` declaration.

`binomialRegulator N hN` implements the nonphysical weights
$c_j=(-1)^j\binom Nj$, $1\le j\le N$, with scales $b_j=j$.
The constructor only checks the normalization of the weights. The geometric
application additionally chooses even $N>\dim Y$ and establishes the spectral
hypotheses.

`orderFour` gives the weights $(-4,6,-4,1)$ and scales $(1,2,3,4)$. Its grouped
factor is algebraically the familiar expression

$$
\frac{x(x+2iM)^6(x+4iM)}{(x+iM)^4(x+3iM)^4}.
$$

### Majorana and other dimensions

The formal analytic theorem does not mention dimension. It applies whenever the
listed spectral hypotheses hold.

The code also proves

$$
e^{i\Theta_M/2}\longrightarrow e^{-i\pi\eta_{\mathrm{heat}}/4},
\qquad (e^{i\Theta_M/2})^2=e^{i\Theta_M}.
$$

This is a statement about a specified real half lift. Identifying it with a
Majorana Pfaffian requires the real/quaternionic structure, spectral pairing, and
compatible Pfaffian normalization. None of those geometric constructions is
formalized here. A principal square root of the determinant is not substituted
for a Pfaffian.

Zero modes are excluded from the massless theorem. A primed spectrum may be
used after removing them, but the code does not reconstruct the full partition
function, its zero-mode factors, or the negative-mass formula.

## Trust and verification

The project contains no `sorry`, `admit`, custom `axiom`, or `native_decide`
proofs. `PVEta/Audit.lean` audits every kernel-safe declaration in the `PVEta` namespace and
prints the axiom dependencies of the principal results.
The recorded dependencies are the standard Lean foundations:
`propext`, `Classical.choice`, and `Quot.sound`.

`./scripts/check.sh` builds the library, checks the audit file with warnings
regarded as errors, and verifies this allowed axiom list. It does not rely on
searching source text alone to detect missing proofs. The recorded local build
and audit output are in [`verification/`](verification/).

Axiom auditing does **not** audit the meaning of a theorem or remove its local
hypotheses. Review `SpectralHypotheses` and the actual theorem signatures before
citing the result. The GitHub Actions workflow is provided for independent
reproduction; inclusion of the workflow is not a claim that a hosted CI run has
already occurred.

This repository was written with AI assistance and checked by Lean. Kernel
checking establishes the formal implications; mathematical review is still
needed to assess their correspondence with the intended geometric statement.

A suitably limited description is:

> The scalar identities and the spectral phase-convergence argument are
> formally verified in Lean, under explicitly stated spectral summability and
> absolute heat-integrability hypotheses.

## References

- E. Witten, *Fermion Path Integrals and Topological Phases*,
  [arXiv:1508.04715](https://arxiv.org/abs/1508.04715), especially §2.1.3.
- J.-M. Bismut and D. S. Freed, *The Analysis of Elliptic Families II: Dirac
  Operators, Eta Invariants, and the Holonomy Theorem*, Commun. Math. Phys.
  **107** (1986), 103–163.
- R. Ponge, *A new proof of the local regularity of the eta invariant of a Dirac
  operator*,
  [arXiv:math/0411123](https://arxiv.org/abs/math/0411123).
- X. Dai and D. S. Freed, *Eta-Invariants and Determinant Lines*,
  [arXiv:hep-th/9405012](https://arxiv.org/abs/hep-th/9405012).
- D. S. Freed and G. W. Moore, *Setting the Quantum Integrand of M-theory*,
  [arXiv:hep-th/0409135](https://arxiv.org/abs/hep-th/0409135).

The Lean code is an explicit formalization of the stated conditional analytic
results; these references are not claimed to contain this exact Lean theorem.
