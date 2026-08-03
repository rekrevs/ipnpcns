# Evidence Matrix for the Formalization Process History

## Purpose and method

This file is the drafting ledger for the process-history report. It is not a
substitute for the report and it is not a claim that the repository records every
moment of work. Its purpose is to prevent retrospective narrative from outrunning
the surviving evidence.

Each evidence item has one of five provenance classes:

- **C - contemporaneous record:** a task log or specification written as the work was
  scoped, implemented, and closed;
- **D - steering decision:** a project-control review or owner decision that records
  the available evidence, uncertainty, and selected direction at a gate;
- **G - Git state:** a dated commit, diff, or tree measurement that records what was
  actually preserved;
- **R - retrospective audit:** a later source, trust, or coverage review. These items
  can corroborate earlier records but must not be presented as knowledge that was
  already available at the earlier date;
- **S - session trace:** the contemporaneous machine-readable record of user and
  agent messages, tool calls, full patch events, compiler outputs, and scratch-file
  migrations. The report uses observable events only, not model-internal reasoning.

The task logs are detailed but self-reported. Git establishes file content and order,
not motivation. Project-control records establish declared decisions, not every
alternative considered. The final source audit establishes conformance of the
finished theorem set, not the correctness of every intermediate interpretation.

## Evidence register

| ID | Class | Primary artifact | Supported historical proposition |
|---|---|---|---|
| E01 | C, G | `LEAN-FEASIBILITY.md`; `wotan/dev-log/T-0001.md`; commit `e291e52` at 17:31:59+02:00 | The work began from a 60-page PDF and no project metadata; it separated mathematical implication from empirical CNS validity, identified library and specification risks, and recommended a Moreau/double-rejection pilot. |
| E02 | C, D, G | `FORMALIZATION-SPEC.md`; PCR/PCD 001; commit `eda50fa` | Before the first headline proof, the project fixed Lean/mathlib versions, norm closure, the non-positive polar sign, arbitrary-Hilbert-space quantification, and explicit non-goals. |
| E03 | C, G | `wotan/dev-log/T-0003.md`; commit `87b1d51` | The pilot constructed a local metric-projection/Moreau API and proved pointwise equality before the closed-hull equality. Dependency materialization briefly failed under restricted network access; no mathematical blocker remained. |
| E04 | C, D, G | `wotan/dev-log/T-0004.md`; PCR 002-003; commit `7a29065` | The longer intersection proof retained the paper's four-Moreau architecture after a possible shorter route was considered; deterministic near-isometry consequences were separated from random-embedding probability. One proof needed a larger heartbeat allowance. |
| E05 | C, D, G | `wotan/dev-log/T-0005.md`; `MODEL-OBLIGATIONS.md`; PCR 004; commit `f0db876` | NNLS mathematics and population interpretation were split. Equation (204), support selection, stochastic convergence, and empirical adequacy became visible interfaces or obligations, while their deterministic consequences were proved. |
| E06 | C, G | `wotan/dev-log/T-0006.md`; commit `084cf8f` | The near-isometry polarization constant and sparse Gram constant were derived directly. A quadratic-form proof replaced a Gershgorin-eigenvalue route because it was shorter and preserved the printed constant. |
| E07 | C, D, G | `wotan/dev-log/T-0007.md`; PCR 005-006; commit `d5f9d34` | Absence of a matching intrinsic polyhedral-face API led to a finite KKT/Moreau certificate that is sufficient, boundary-safe, and explicitly not necessary. This removed equation (199) as a hidden assumption without claiming a full face partition. |
| E08 | C, D, G | `wotan/dev-log/T-0008.md`; PCR 006-007; commit `529e111` | The finite NNLS layer progressed from fixed-point complementarity to global optimality and deterministic convergence under an explicit contraction. The record already notes that the familiar upper step bound alone cannot yield strict coefficient contraction in a rank-deficient design. |
| E09 | C, D, G | `wotan/dev-log/T-0009.md`; PCR 007-008; commit `560c81e` | When the initial queue ended, steering expanded coverage around mathematical dependencies rather than paper order. Intrinsic subspace theorems were completed before matrix pseudoinverse notation, which was split into a later task. |
| E10 | C, D, G | `wotan/dev-log/T-0010.md`; PCR 009; commit `48efc13` | A nonzero prediction kernel was proved to obstruct every strict coefficient-space contraction. The full-row-rank theorem was retained unchanged and rank-deficient convergence was redirected to a Fejer/compactness architecture rather than obtained by strengthening assumptions silently. |
| E11 | C, G | `wotan/dev-log/T-0011.md`; commit `10baf10` | Exact cone laws and circuit rewrites were proved, but the conditional circuit theorem stopped at explicit emptiness-control and strong-blocking premises. A tempting projected-generator membership shortcut was rejected as invalid under closed-hull semantics. |
| E12 | C, G | `wotan/dev-log/T-0012.md`; commit `d6f610a` | Infinite-dimensional infima were not assumed attained. The finite-frame proxy was proved optimistic and received an error bound only under explicit directional coverage. |
| E13 | C, D, G | `wotan/dev-log/T-0013.md`; PCR 011-012; commit `a7ecddb` | Exact occupancy used uniform sampling of distinct targets within each axon and independence between axons. Treating all collaterals as independent draws was recognized as a different experiment and rejected. Exponential and two-message approximations remained named boundaries. |
| E14 | C, D, G | `wotan/dev-log/T-0014.md`; PCR 012-013; commit `b26dcec` | The signal layer selected Bochner `L2` on a restricted finite-window measure. Pointwise identities became almost-everywhere statements; images of closed cones were closed by conic hull; convolution boundary, compactness, and quadratic remainder claims remained explicit interfaces where hypotheses were missing. |
| E15 | C, D, G | `wotan/dev-log/T-0015.md`; PCR 013-014; commit `764a00f` | With no bundled Moore-Penrose API, the project built the inverse from the effective map between the kernel complement and range, covering rectangular and rank-deficient matrices. Dependent projector instances required an extensional equality lemma rather than direct rewriting. |
| E16 | C, D, G | `wotan/dev-log/T-0016.md`; PCR 014-015; commit `94c4bfa` | Rank-deficient projected NNLS convergence was recovered without a lower spectral bound: Fejer descent, summable prediction error, finite-dimensional compactness, and a cluster minimizer yielded convergence of the whole sequence. Prediction uniqueness remained distinct from coefficient uniqueness. |
| E17 | C, D, G | `wotan/dev-log/T-0017.md`; PCR 015-016; commit `af5d096` | The continuous Hann-window dictionary required local exact Fourier integration rather than a packaged library theorem. Its normalization, zero means, Gram matrix, NNLS examples, residual signs, and baseline convention were checked against the rendered paper. |
| E18 | C, D, G | `wotan/dev-log/T-0018.md`; PCR 016-017; commit `08b72d3` | Without a Hilbert-Schmidt operator abstraction, compactness of a nonzero causal Volterra filter was obtained through explicit rank-one operators, simple-function density, and norm closure. Periodic and zero-extension boundary conventions were proved different rather than conflated. |
| E19 | C, D, G | `wotan/dev-log/T-0019.md`; PCR 017-018; commit `a0a608e` | Empty-queue review identified two exact structural claims still hidden behind the active-face discussion. Positive homogeneity and span reduction were proved in an unrestricted ambient Hilbert space; a dependent-instance rewrite failure was bypassed by applying a containment theorem directly. |
| E20 | C, D, G | `wotan/dev-log/T-0020.md`; PCR 018-019; commit `3dd6ff9` | The membrane `O(Delta t^2)` interface was discharged under an explicit Lipschitz drive. A simple `L Delta t^2/tau` bound was selected over the sharper elementary half-factor because it supplied the required uniform quadratic witness with a smaller proof. |
| E21 | C, D, G | `wotan/dev-log/T-0021.md`; PCR 019-021; commit `123d09a` | The exponential occupancy approximation was upgraded from a caller-supplied interface to a constructive lower bound with absolute error at most `m p^2/n`, while invalid regimes stayed separate. |
| E22 | C, D, G | `wotan/dev-log/T-0025.md`; PCR 021-022; commit `367a1c8` | The two-message overlap boundary was exactified for a literal Cartesian-product experiment. Independence became structural in that chosen model, not an inferred fact about biological messages. This was the final compact theorem target before source audit. |
| E23 | R, D, G | `SOURCE-AUDIT.md`; `wotan/dev-log/T-0022.md`; PCR 022-023; commit `fd1361b` | The author-supplied archive was inventoried, compiled, and compared with the distributed PDF; source-to-Lean tracing reached equation (210). No material proof discrepancy was found. One section reference and one documentation coverage gap were corrected. The final build had 2,960 jobs, no admitted/custom/unsafe declarations, and a 38-endpoint audit reported only the accepted standard axioms. |
| E24 | R, G | `wotan/dev-log/T-0023.md`; PCR 024; commit `5a83b13` | A separate 24-page scientific report was compiled and visually inspected page by page. Its typography required several render-correct loops, and it deliberately omitted task chronology so that this history could serve a different purpose. |
| E25 | G | `git log --reverse --format=...`; current Lean tree measurement | The preserved commits from feasibility through source audit span 17:31:59-22:36:58 on 2026-08-03; the scientific report commit follows at 23:05:38. The final Lean tree contains 31 module files under `IPNPCNS/`, 8,367 Lean lines including the root module, 439 theorem/lemma declarations, and 172 definitions/structures/classes. Commit timestamps establish repository order and elapsed clock time between commits, not human-equivalent effort or uninterrupted execution. |
| E26 | S | `reports/session-trace-audit.md`; main Codex session prefix SHA-256 `80e1b5977d4ff07fbfc696f319eb2a31db33d57636464e20b81d1063ba763ba5` | The 6,276-record audited prefix preserves 427 successful patch events. It includes 174 add/update/delete events over 33 scratch, probe, or axiom-audit files, their compiler diagnostics, and migrations into permanent modules. It supports reconstruction of discarded proof code and correction loops that are absent from Git. |

## Narrative claim matrix

| Claim | Required evidence | Drafting constraint |
|---|---|---|
| Formalization was progressive contract refinement, not direct transcription. | E01-E07, E14, E20-E23 | Show concrete changes in theorem signatures and boundaries; do not use the thesis as a slogan. |
| The coordinate-free cone pilot determined the architecture. | E02-E04, E09, E15 | Distinguish what the pilot demonstrated from later broad coverage. |
| Work expanded by dependency and risk, not by paper order. | E04-E09, E13-E19 | Use a dependency diagram and selected gates, not a commit diary. |
| Failed or blocked approaches produced mathematical information. | E03, E07, E10-E12, E14-E20, E23, E26 | Separate technical inconvenience from a genuine counterexample, proof-route change, or theorem-boundary correction. Use session-trace detail where Wotan gives only the summary. |
| Interfaces were not permanent admissions: some were later discharged. | E05, E13-E14, E18, E20-E22 | Contrast equation (204), which remains a model premise, with membrane and occupancy interfaces that became theorems. |
| The verification standard strengthened over time. | E02-E04, E09-E18, E23-E24 | Present build, gap scan, endpoint axiom audit, source audit, and page QA as increasing layers, not as interchangeable checks. |
| Source conformance was a late independent gate. | E22-E23 | Label this as retrospective corroboration; never imply LaTeX-source knowledge guided the early proofs. |
| The result is broad but not a line-by-line or empirical verification. | E01, E05, E14, E23 | Name the residual mathematical and empirical boundaries. |
| The compressed calendar is real but not directly comparable to the initial human estimate. | E01, E25 | State what Git timestamps do and do not measure; avoid productivity claims unsupported by controlled comparison. |

## Negative evidence and residual uncertainty

- The session trace preserves the full add/update/delete payload for every recorded
  tool-mediated patch in the audited prefix, including the principal abandoned
  scratch proofs. This is substantially more complete than Git. It is not a record of
  unexpressed cognition, and the report does not claim that instrumentation captures
  every possible process state.
- Wotan and project-control entries were maintained within the same work session and
  are contemporaneous project records, but they remain authored summaries rather than
  independent observations.
- Git order is reliable for preserved states; commit timestamps alone do not measure
  active compute time, review time, or equivalent human effort.
- The source audit found no material discrepancy in claimed coverage. It does not turn
  explicitly out-of-scope results into verified theorems.
- Build success checks elaboration and kernel acceptance. It is complemented, not
  replaced, by theorem-signature review, gap scans, axiom audits, source conformance,
  and mathematical interpretation.
