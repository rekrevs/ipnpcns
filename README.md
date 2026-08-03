# IPNPCNS

This repository contains a Lean 4 formalization of the mathematical core of
*Information Processing by Neuron Populations in the Central Nervous System: A
Theory of the Mathematical Structure of Data and Operations*
([source paper](2309.02332v3.pdf)). The development studies closed-cone algebra,
finite subspace representations, nonnegative least squares, deterministic signal
operators, sparse occupancy, and conditional neural-population realizations.

The project verifies mathematical consequences of explicit assumptions. It does
not claim that biological neural systems satisfy those assumptions.

## Read the reports

The two reports are the best entry points to the project:

| Report | Focus | PDF | LaTeX source |
|---|---|---|---|
| **Scientific formalization report** | A self-contained account of the mathematics, the verified results, the trust boundary, and the remaining model obligations. Written for mathematically mature readers; no Lean expertise is assumed. | **[Read the PDF](output/pdf/ipnpcns-scientific-formalization-report.pdf)** | [Source](reports/scientific-formalization-report.tex) |
| **Formalization process history** | An evidence-based reconstruction of how the definitions, proof architecture, failures, audits, and final verification were developed. | **[Read the PDF](output/pdf/ipnpcns-formalization-process-history.pdf)** | [Source](reports/formalization-process-history.tex) |

The scientific report should be read first for the result itself. The process
history is complementary: it explains how the result was reached and what the
development record reveals about machine-assisted formalization.

## What has been verified

The compiled development consists of 31 substantive Lean modules, 8,367 lines,
and 439 theorem or lemma declarations. Its main results include:

- Moreau decomposition for arbitrary closed convex cones in arbitrary real
  Hilbert spaces;
- the identity expressing conic projection as two successive conic rejections;
- three closure-safe, rejection-only formulas for cone intersection;
- finite-subspace identities and Moore-Penrose representations, including
  rank-deficient rectangular matrices;
- deterministic near-isometry, polarization, and sparse-Gram estimates;
- fixed-point, optimality, spectral, full-rank, and rank-deficient convergence
  results for finite nonnegative least squares;
- a finite-window `L2` signal model, an exact orthonormal wavelet example, a
  compact causal Volterra operator, and a quantified membrane-update remainder;
- exact finite collateral-occupancy and independent two-message overlap formulas;
- conditional active-face, population-approximation, and cone-circuit theorems.

The full build contains no `sorry`, custom axioms, or unsafe declarations. The
principal endpoint audit reports only Lean and mathlib's standard foundational
principles.

## Verification boundary

Formal verification makes the assumptions precise; it does not make them
empirical facts. In particular, this repository does not establish anatomical
connectivity, biological support selection, in-vivo learning convergence, or
numerical error levels for real neural populations. Stochastic learning, a general
Laplace-domain filter realization, random Johnson-Lindenstrauss guarantees, and
recurrent-network stability also remain outside the compiled theorem set.

See [Model and Learning Obligations](MODEL-OBLIGATIONS.md) for the detailed boundary
and [LaTeX Source Conformance Audit](SOURCE-AUDIT.md) for equation-level comparison
with the author-supplied source archive.

## Repository guide

| Path | Contents |
|---|---|
| [`IPNPCNS/`](IPNPCNS/) | Lean modules, organized by mathematical layer |
| [`IPNPCNS.lean`](IPNPCNS.lean) | Root import for the verified corpus |
| [`FORMALIZATION-SPEC.md`](FORMALIZATION-SPEC.md) | Formal scope, conventions, and acceptance criteria |
| [`LEAN-FEASIBILITY.md`](LEAN-FEASIBILITY.md) | Initial feasibility assessment and formalization strategy |
| [`MODEL-OBLIGATIONS.md`](MODEL-OBLIGATIONS.md) | Explicit assumptions, exclusions, and empirical obligations |
| [`SOURCE-AUDIT.md`](SOURCE-AUDIT.md) | Audit against the supplied LaTeX source and distributed paper |
| [`reports/`](reports/) | English LaTeX sources and report evidence records |
| [`output/pdf/`](output/pdf/) | Publication-ready report PDFs |
| [`wotan/`](wotan/) | Structured task ledger and development logs |

## Build and check the formalization

The repository pins Lean and mathlib through `lean-toolchain` and
`lake-manifest.json`. With [Elan](https://github.com/leanprover/elan) installed:

```console
git clone https://github.com/rekrevs/ipnpcns.git
cd ipnpcns
lake exe cache get
lake build
```

The verified environment is Lean 4.31.0 with mathlib 4.31.0. A successful
`lake build` checks the complete import graph rooted at `IPNPCNS.lean`.

## Reproducibility and source conformance

The tracked source paper is
[`2309.02332v3.pdf`](2309.02332v3.pdf). After the Lean proofs were complete, the
mathematical statements were independently checked against the author-supplied
LaTeX archive. The source was rebuilt, compared with the distributed PDF, and
audited equation by equation. The audit found no material mathematical discrepancy
in the claims made by this formalization; its artifact hashes and precise coverage
classifications are recorded in [`SOURCE-AUDIT.md`](SOURCE-AUDIT.md).

The supplied archive itself is intentionally not versioned. It is a redundant
upstream artifact whose identity is fixed by the recorded SHA-256 digest; temporary
extraction and report-build products are likewise excluded from Git.
