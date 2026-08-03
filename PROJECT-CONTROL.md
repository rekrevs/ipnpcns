# Project control log

- Protocol: `project-control/v0.1`

## PCR-2026-08-03-001

- Record type: review
- Date: 2026-08-03
- Mode: direction-review
- Trigger: The feasibility assessment completed and the owner requested continuous,
  autonomous execution of all planned and newly discovered formalization work.
- Control judgement: continue, operate, evaluate
- Current gate: A paper-faithful Lean specification and a compiling project foundation
  have not yet been established.
- Recommendation: Activate the four planned work packages, execute them through Wotan,
  and use a checkpoint after the double-rejection theorem to redirect or decompose
  subsequent work based on compiler evidence.
- Owner decision required: none
- Evidence:
  - `LEAN-FEASIBILITY.md`
  - `wotan/dev-log/T-0001.md`
  - Owner instruction on 2026-08-03 to continue autonomously and resolve questions
    through project control where possible.
- Uncertainty:
  - The paper's headline cone identities appear sound under manual review, but Moreau
    infrastructure and closure-sensitive cone operations are not bundled in mathlib.
  - Sections 3 and 5 contain assumptions that must be separated from derived claims.
- Proposed actions:
  - Activate T-0002 through T-0005.
  - Establish a version-pinned Lean project and formal specification in T-0002.
  - Treat a compiling, assumption-audited proof of (98)/(108) as the first scientific
    and architectural gate.
- Revisit when:
  - T-0003 completes or exposes a foundational mismatch.
  - A paper claim is false under its stated assumptions.
  - The workable Wotan queue becomes empty.

## PCD-2026-08-03-001

- Record type: decision
- Date: 2026-08-03
- Decides review: `PCR-2026-08-03-001`
- Owner: Sverker
- Decision: Execute all current and necessary follow-on formalization tasks
  continuously and autonomously; make in-scope decisions through project control and
  stop only at a genuinely impossible situation.
- Disposition: approved
- Resulting Wotan tasks: T-0002, T-0003, T-0004, T-0005
- Portfolio signal: The project is receiving sustained implementation attention.
- Revisit when:
  - T-0003 completes or exposes a foundational mismatch.
  - A scientific or technical gate cannot be resolved from project evidence.
  - All approved work is complete.

## PCR-2026-08-03-002

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0003 completed the first scientific and architectural gate.
- Control judgement: continue, operate
- Current gate: The longer intersection identity (109) is the next unverified
  structural claim; deterministic approximation results should not obscure that gate.
- Recommendation: Continue with T-0004, proving the intersection identity first and
  decomposing approximate invariance or Gershgorin work if either requires independent
  infrastructure.
- Owner decision required: none; PCD-2026-08-03-001 already authorizes continuous
  execution and in-scope decomposition.
- Evidence:
  - `IPNPCNS/Cone/MetricProjection.lean`
  - `IPNPCNS/Cone/Moreau.lean`
  - `IPNPCNS/Cone/DoubleRejection.lean`
  - `wotan/dev-log/T-0003.md`
- Uncertainty:
  - The paper's intersection proof is substantially longer than double rejection and
    may benefit from a shorter equivalent proof using polar identities.
  - The exact hypotheses needed for the printed projection-error constant remain to
    be compiler- and algebra-checked.
- Revisit when:
  - The intersection identity compiles.
  - The approximation theorem requires a material correction or new owner-owned scope.

## PCR-2026-08-03-003

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0004 proved the intersection identity and deterministic projection-error
  theorem.
- Control judgement: continue, operate
- Current gate: The conditional population model is now the highest-value unverified
  paper layer; polarization and Gershgorin are independent reusable endpoints.
- Recommendation: Continue with T-0005, preserving every learning and biological
  premise as an explicit hypothesis. Execute T-0006 afterward to close the remaining
  deterministic approximation endpoints.
- Owner decision required: none; PCD-2026-08-03-001 authorizes continuation and
  decomposition.
- Evidence:
  - `IPNPCNS/Cone/Intersection.lean`
  - `IPNPCNS/Approx/Invariance.lean`
  - `wotan/dev-log/T-0004.md`
- Uncertainty:
  - The full NNLS convergence discussion cannot be recovered from “standard
    assumptions”; only precisely stated finite or conditional results are admissible.
  - The sharp (162) constant and support bookkeeping for (171) may require more
    infrastructure than their paper-level derivations suggest.
- Revisit when:
  - T-0005 establishes the conditional population boundary.
  - T-0006 exposes a mismatch in either printed constant.

## PCR-2026-08-03-004

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0005 established the conditional learning and population-model boundary.
- Control judgement: continue, operate
- Current gate: The remaining deterministic approximation endpoints should be closed
  before expanding the conditional face and learning interfaces into constructive
  theorems.
- Recommendation: Execute T-0006 next. Then construct active-face projection regions
  in T-0007 and prove finite NNLS optimality and deterministic convergence in T-0008.
- Owner decision required: none; PCD-2026-08-03-001 already authorizes continuous
  execution and creation of necessary follow-on work.
- Evidence:
  - `IPNPCNS/Learning/NNLS.lean`
  - `IPNPCNS/Model/Population.lean`
  - `MODEL-OBLIGATIONS.md`
  - `wotan/dev-log/T-0005.md`
- Uncertainty:
  - The paper's stochastic statements remain underspecified and cannot be promoted to
    theorems without adding a probability model.
  - A useful constructive face theorem may initially need a finite generating family
    and an explicitly selected active set rather than the paper's informal regions.
- Proposed actions:
  - Complete the sharp polarization and sparse Gram bounds in T-0006.
  - Replace the conditional equation (199) field with sufficient polyhedral
    hypotheses in T-0007.
  - Extend fixed-point complementarity to minimizer equivalence and a precisely
    scoped deterministic convergence theorem in T-0008.
- Revisit when:
  - T-0006 resolves or corrects the printed constants.
  - T-0007 identifies the precise face-selection hypotheses.

## PCR-2026-08-03-005

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0006 verified the sharp constants in equations (162) and (171).
- Control judgement: continue, operate
- Current gate: Equation (199) remains an assumed field; a constructive active-face
  theorem is the next bridge from cone geometry to the population interface.
- Recommendation: Execute T-0007 using finite generators and KKT-style sufficient
  conditions. Prefer a theorem that constructs `projection_eq_face` over a selected
  region; defer an intrinsic relative-interior equivalence if it is not needed for
  that bridge.
- Owner decision required: none; PCD-2026-08-03-001 authorizes the selected
  continuation.
- Evidence:
  - `IPNPCNS/Approx/Polarization.lean`
  - `IPNPCNS/Approx/SparseGram.lean`
  - `wotan/dev-log/T-0006.md`
- Uncertainty:
  - Mathlib may represent finitely generated cones through positive spans rather than
    a specialized polyhedral-cone type.
  - The paper's phrase “region associated with a face” does not specify boundary tie
    handling; sufficient active-set inequalities are likely the faithful first target.
- Proposed actions:
  - Define the selected generator cone and active face span.
  - State primal-membership, residual-polar, and complementarity conditions that
    certify the face-span projection as the cone projection.
  - Instantiate the T-0005 population interface from the certificate.
- Revisit when:
  - T-0007 yields a constructive equation (199).
  - Degenerate active sets expose a scope mismatch that affects the population model.

## PCR-2026-08-03-006

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0007 replaced conditional equation (199) with a finite active-face
  certificate and resolved zero-face and boundary behavior.
- Control judgement: continue, operate
- Current gate: The finite NNLS layer still identifies fixed points with
  complementarity but does not connect those points to global minimizers or a
  deterministic iteration theorem.
- Recommendation: Execute T-0008 next. Prove algebraic gradient correctness and
  complementarity/minimizer equivalence first; select the strongest bounded
  deterministic convergence endpoint supported by mathlib and explicit spectral or
  contraction hypotheses.
- Owner decision required: none; PCD-2026-08-03-001 authorizes continuation.
- Evidence:
  - `IPNPCNS/Model/ActiveFace.lean`
  - `IPNPCNS/Model/Population.lean`
  - `wotan/dev-log/T-0007.md`
- Uncertainty:
  - An intrinsic polyhedral relative-interior partition remains outside the available
    API, but it is not required for the verified sufficient projection regions.
  - A general projected-gradient convergence development may be disproportionate to
    the paper's underspecified learning statement; a finite quadratic contraction
    theorem may be the appropriate verified endpoint.
- Proposed actions:
  - Prove the finite quadratic loss-difference and gradient identities.
  - Derive global optimality from complementarity and the positive-semidefinite Gram
    remainder, including the converse through feasible coordinate perturbations.
  - Formalize deterministic convergence only under a theorem signature strong enough
    to make every stability premise visible.
- Revisit when:
  - T-0008 establishes the deterministic learning boundary.
  - The remaining paper-coverage queue needs to be expanded.

## PCR-2026-08-03-007

- Record type: review
- Date: 2026-08-03
- Mode: direction-review
- Trigger: T-0008 completed the finite deterministic NNLS layer and the prior Wotan
  queue reached its final planned task.
- Control judgement: continue, operate, evaluate
- Current gate: Broad paper coverage now depends on the finite subspace/projector
  layer that precedes both the cone generalization and the spectral learning results.
- Recommendation: Execute T-0009 as the next foundation, followed by the finite Gram
  step-size bridge in T-0010. Then close the remaining exact cone/circuit laws, cone
  comparison bounds, sparsity calculation, and deterministic signal abstraction in
  T-0011 through T-0014.
- Owner decision required: none; PCD-2026-08-03-001 authorizes continuous expansion
  into necessary paper-coverage tasks.
- Evidence:
  - `IPNPCNS/Learning/NNLSOptimality.lean`
  - `IPNPCNS/Learning/NNLSConvergence.lean`
  - `LEAN-FEASIBILITY.md`
  - `FORMALIZATION-SPEC.md`
  - Section inventory from `tmp/pdfs/paper.txt`
- Uncertainty:
  - Moore–Penrose matrix identities may require a local finite pseudoinverse layer;
    coordinate-free subspace theorems should be preserved even if that layer is
    decomposed.
  - Signal/filter results need theorem-by-theorem analytic hypotheses absent from the
    prose and may terminate at an explicit conditional interface.
  - Stochastic learning, random JL embeddings, and biological adequacy remain
    intentionally outside deterministic proof claims unless fully specified.
- Proposed actions:
  - Formalize Section 2 subspace operations and projector comparisons in T-0009.
  - Derive `BatchLinearContraction` from singular-value bounds in T-0010.
  - Verify equations (93)–(97), (209), and the abstract conditional (210) in T-0011.
  - Verify cone similarity/frame-proxy claims (87)–(92) in T-0012.
  - Separate exact occupancy probability from the independence approximation in
    equation (30) in T-0013.
  - Build a precise deterministic signal/filter layer for Sections 3.1–3.3 in T-0014.
- Revisit when:
  - T-0009 determines the Moore–Penrose scope.
  - T-0011 closes the remaining exact cone-algebra surface.
  - T-0014 reaches an analytic or empirical specification boundary.

## PCR-2026-08-03-008

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0009 completed the intrinsic finite subspace algebra, matrix-range
  identity, and projector comparison layer, and exposed the exact Moore--Penrose
  representation boundary.
- Control judgement: continue, operate, preserve
- Current gate: T-0010 can now use finite adjoint/range infrastructure to derive the
  NNLS spectral contraction. Moore--Penrose notation is not on that dependency path.
- Recommendation: Continue with T-0010. Preserve exact pseudoinverse projector
  spellings as T-0015, ordered after the higher-value deterministic coverage queue but
  already actionable from T-0009.
- Owner decision required: none; PCD-2026-08-03-001 authorizes both continuation and
  creation of necessary follow-on tasks.
- Evidence:
  - `IPNPCNS/Subspace/Basic.lean`
  - `IPNPCNS/Subspace/FiniteMatrix.lean`
  - `IPNPCNS/Subspace/Comparison.lean`
  - `IPNPCNS/Subspace/Examples.lean`
  - `wotan/dev-log/T-0009.md`
- Uncertainty:
  - A maintainable Moore--Penrose implementation may require a reusable spectral or
    singular-value layer rather than a short matrix definition.
  - The paper gains no additional geometric theorem from the `A A⁺` spelling, so it
    should not delay contraction, cone, probability, or signal coverage.
- Proposed actions:
  - Execute T-0010 next.
  - Retain T-0015 as READY and execute it after earlier queue entries unless another
    task establishes a direct dependency.
- Revisit when:
  - T-0010 settles the full-row-rank and rank-deficient learning split.
  - T-0015 selects a concrete Moore--Penrose construction.

## PCR-2026-08-03-009

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0010 derived the paper's full-row-rank step interval and proved the
  obstruction to strict coefficient contraction in the rank-deficient case.
- Control judgement: continue, operate, preserve
- Current gate: The next dependency is the remaining exact cone/circuit algebra in
  T-0011. Rank-deficient NNLS convergence needs a different proof architecture but no
  owner decision.
- Recommendation: Continue with T-0011. Preserve rank-deficient convergence as
  T-0016, following the existing coverage queue, using Fejér monotonicity or averaged
  operators rather than weakening T-0010's strict theorem.
- Owner decision required: none; the distinction is mathematically forced by the
  nontrivial kernel theorem.
- Evidence:
  - `IPNPCNS/Learning/NNLSSpectral.lean`
  - `IPNPCNS/Learning/NNLSConvergence.lean`
  - `wotan/dev-log/T-0010.md`
- Uncertainty:
  - A local finite-dimensional convergence argument may be needed because mathlib's
    generic averaged-operator API is limited.
  - The exact selected coefficient limit can depend on initialization, although its
    prediction is unique.
- Proposed actions:
  - Execute T-0011 next.
  - Execute T-0016 after the earlier paper-coverage and Moore--Penrose tasks unless a
    dependency makes it urgent.
- Revisit when:
  - T-0011 closes the exact cone/circuit layer.
  - T-0016 selects its convergence mechanism.

## PCR-2026-08-03-010

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0011 completed equations (93)--(97), reflection law (209), the exact
  primitive projection/intersection circuits, and conditional equation (210).
- Control judgement: continue, operate
- Current gate: T-0012 must make the nonempty unit-direction and finite-frame
  conventions in equations (87)--(92) explicit before their infima and minima can be
  compared.
- Recommendation: Execute T-0012 next. Define exact directional similarity and the
  finite proxy with explicit witnesses, prove the unit interval and polar-zero
  statements, and derive the one-sided coverage error from metric-projection
  nonexpansiveness. Keep empty cones and empty frames outside the main theorem.
- Owner decision required: none; PCD-2026-08-03-001 authorizes continuation and the
  paper already states that the empty cone is handled separately.
- Evidence:
  - `IPNPCNS/Cone/Laws.lean`
  - `IPNPCNS/Model/Circuits.lean`
  - `wotan/dev-log/T-0011.md`
- Uncertainty:
  - A direct `sInf` formulation may require explicit boundedness and nonemptiness
    lemmas, while finite proxy minima need nonempty finite frames.
  - The angular form (89) should remain a derived definition unless an arccos theorem
    adds scientific value beyond the similarity bounds.
- Proposed actions:
  - Execute T-0012.
  - Preserve the exact versus proxy distinction and do not assert a uniform error
    estimate in the absence of directional coverage.
- Revisit when:
  - T-0012 settles the infimum/minimum representation and coverage theorem.

## PCR-2026-08-03-011

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0012 completed the exact cone similarity, angular consequences, finite
  normalized-frame proxy, and coverage-error theorem (92).
- Control judgement: continue, operate
- Current gate: Equation (30) mixes an exact occupancy expectation with an
  exponential approximation and a second, explicitly additional overlap
  approximation.
- Recommendation: Execute T-0013 next. Model each active axon as choosing a uniform
  `p`-subset of `n` targets, independently across the `m` axons. Prove the occupied
  target expectation by indicator variables. Keep the exponential replacement and
  two-message overlap as separately named approximations or conditional error
  interfaces rather than equalities.
- Owner decision required: none; the paper explicitly states the sampling and
  approximation boundaries.
- Evidence:
  - `IPNPCNS/Cone/Comparison.lean`
  - `wotan/dev-log/T-0012.md`
  - equation (30) and its surrounding paragraph in `tmp/pdfs/paper.txt`
- Uncertainty:
  - Mathlib's uniform finite-subset probability API may be heavier than a direct
    finite probability-mass-function model.
  - A quantitative exponential approximation is optional unless it can be obtained
    with a short, explicit bound; it must not obscure the exact expectation.
- Proposed actions:
  - Execute T-0013 using finite indicator expectations and explicit parameter guards
    `p ≤ n`.
  - Treat `n = 0`, `m = 0`, and impossible collateral counts explicitly.
- Revisit when:
  - T-0013 establishes the exact occupancy theorem and fixes the approximation
    interfaces.

## PCR-2026-08-03-012

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0013 proved the exact finite occupancy formula (30), handled parameter
  boundaries, and isolated both subsequent approximations.
- Control judgement: continue, operate, preserve
- Current gate: T-0014 must choose a precise finite-interval signal type and bounded
  temporal-filter interface without overcommitting to an underspecified convolution
  boundary convention or the informal `O(Δt²)` in equation (33).
- Recommendation: Execute T-0014 next. Use Bochner `L²` on a finite interval for
  scalar and finite-vector signals, lift finite spatial matrices pointwise, and state
  temporal filters as bounded linear operators. Prove aggregation, linearity,
  boundedness, cone-image, and finite-dictionary consequences. Preserve convolution,
  compactness, Laplace-domain, and discretization claims behind explicit operator or
  remainder hypotheses unless the paper supplies the missing regularity.
- Owner decision required: none; this is the smallest faithful deterministic layer
  and follows PCD-2026-08-03-001.
- Evidence:
  - `IPNPCNS/Probability/Occupancy.lean`
  - `wotan/dev-log/T-0013.md`
  - Sections 3.1--3.3 in `tmp/pdfs/paper.txt`
- Uncertainty:
  - Mathlib's Bochner-space notation and pointwise matrix lifting may require a
    measurable-function representative rather than a simple function definition.
  - Compactness of truncated convolution depends on the exact kernel extension and
    integration domain; a bounded-operator interface is sufficient for the paper's
    deterministic algebra.
- Proposed actions:
  - Execute T-0014 with visible measure, boundedness, and remainder premises.
  - Preserve exact wavelet examples and convolution compactness as follow-on tasks if
    they become separable after the core signal layer.
- Revisit when:
  - T-0014 establishes the signal/filter boundary and determines any justified
    follow-on tasks.

## PCR-2026-08-03-013

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0014 established the finite-window Bochner `L²` signal layer, bounded
  spatial and temporal operators, conic aggregation, finite dictionaries, and an
  explicit discretization remainder boundary.
- Control judgement: continue, operate, preserve
- Current gate: T-0015 remains the next general mathematical gap: the paper's
  Moore--Penrose projector spellings are not yet connected to the intrinsic subspace
  theorems. The exact wavelet and concrete convolution claims are now separable and
  no longer block the deterministic abstraction.
- Recommendation: Execute T-0015 next, preserving the no-full-rank requirement and
  using finite-dimensional orthogonal decomposition if a complete SVD API would add
  unnecessary scope. Keep T-0016 next in the optimization queue. Schedule the exact
  Hann dictionary as T-0017 and a concrete compact convolution construction as
  T-0018 after those algebraic obligations.
- Owner decision required: none; the ordering reduces shared-foundation risk and is
  authorized by PCD-2026-08-03-001.
- Evidence:
  - `IPNPCNS/Signal/Deterministic.lean`
  - `MODEL-OBLIGATIONS.md`
  - `wotan/dev-log/T-0014.md`
  - Sections 3.1--3.3 in `tmp/pdfs/paper.txt`
- Uncertainty:
  - Mathlib still has no bundled general Moore--Penrose matrix inverse.
  - Exact trigonometric integration and compact convolution may each require reusable
    analysis infrastructure; they should not be mixed into the matrix task.
- Proposed actions:
  - Execute T-0015 and prove all four Penrose equations before projector corollaries.
  - Execute T-0016 using a Fejér or averaged-operator argument without a positive
    lower singular-value premise.
  - Retain T-0017 and T-0018 as explicit later analytic coverage.
- Revisit when:
  - T-0015 selects and verifies a maintainable pseudoinverse construction.

## PCR-2026-08-03-014

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0015 constructed the finite real Moore--Penrose inverse, proved its
  uniqueness and all four Penrose equations, and recovered the paper's matrix
  renderings through equation (22).
- Control judgement: continue, operate
- Current gate: T-0016 is the remaining deterministic learning gap. Strict
  coefficient contraction is correctly impossible in the rank-deficient case, but
  convergence to the nonempty minimizer set has not yet been established.
- Recommendation: Execute T-0016 next. Work in the finite coefficient Euclidean
  space, prove a Fejér descent inequality for the projected-gradient map from the
  upper spectral bound and `0 < ε < 2/L`, derive square-summable steps and cluster
  point optimality, and use finite-dimensional compactness plus Fejér monotonicity to
  identify a limit. Do not add a positive lower singular-value bound.
- Owner decision required: none; the rank-deficient endpoint and its scope were fixed
  by PCR-2026-08-03-009.
- Evidence:
  - `IPNPCNS/Subspace/MoorePenrose.lean`
  - `IPNPCNS/Subspace/Basic.lean`
  - `IPNPCNS/Subspace/FiniteMatrix.lean`
  - `wotan/dev-log/T-0015.md`
- Uncertainty:
  - Mathlib may not expose an end-to-end finite-dimensional Fejér convergence theorem
    with the exact hypotheses needed here.
  - A direct subsequence/compactness proof may be shorter and more auditable than
    adapting a generic fixed-point iteration hierarchy.
- Proposed actions:
  - Execute T-0016 without a lower spectral bound.
  - Reuse T-0008's minimizer/fixed-point equivalence and T-0010's common-prediction
    theorem rather than reproving optimization algebra.
- Revisit when:
  - T-0016 establishes convergence to a selected minimizer or exposes a genuinely
    missing compactness lemma.

## PCR-2026-08-03-015

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0016 established rank-deficient projected NNLS convergence under an
  upper spectral bound and `0 < ε < 2/L`, including asymptotic regularity and a
  selected coefficient minimizer.
- Control judgement: continue, operate, preserve
- Current gate: The deterministic learning chain is closed. T-0017 is now the next
  approved gap: the abstract finite dictionary interface from T-0014 should be tied
  to the paper's concrete finite Hann-window wavelet construction.
- Recommendation: Execute T-0017 next. Isolate the exact discrete indexing,
  normalization, and boundary convention before proving orthogonality. Prefer a
  finite algebraic statement faithful to the paper over importing an unjustified
  continuous-wavelet interpretation. Keep T-0018 queued after T-0017 for the concrete
  compact convolution operator.
- Owner decision required: none; T-0017 and T-0018 were already approved by
  PCR-2026-08-03-013.
- Evidence:
  - `IPNPCNS/Learning/NNLSRankDeficient.lean`
  - `IPNPCNS/Learning/NNLSSpectral.lean`
  - `wotan/dev-log/T-0016.md`
  - `MODEL-OBLIGATIONS.md`
- Uncertainty:
  - The paper's exact Hann discretization may contain an implicit endpoint or
    indexing convention that must be made explicit.
  - A literal trigonometric orthogonality proof may require finite Fourier identities
    not already packaged in the repository.
- Proposed actions:
  - Close T-0016 after the full build and axiom audit.
  - Execute T-0017 and record any convention-sensitive claim as an explicit theorem
    premise or corrected finite formula.
  - Continue to T-0018 once the dictionary boundary is stable.
- Revisit when:
  - T-0017 has either verified the exact finite dictionary or identified a concrete
    counterexample in the paper's stated convention.

## PCR-2026-08-03-016

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0017 verified the paper's exact finite Hann-window dictionary, including
  its normalization, orthonormality, zero means, three NNLS examples, and explicit
  baseline-subtraction convention.
- Control judgement: continue, operate, preserve
- Current gate: The remaining approved analytic gap is T-0018: T-0014 deliberately
  left concrete finite-window convolution and compactness behind named interfaces.
  T-0017 exposed no contradiction or dependency that should displace that gate.
- Recommendation: Execute T-0018 next with the causal-truncation convention. Start
  from the nontrivial unit-step impulse response, whose operator is the Volterra map
  `x ↦ (t ↦ ∫ s in 0..t, x s)`. Construct it on recording-window `L²`, prove a
  concrete norm bound, and prove compactness through uniform finite-rank step
  approximants. Treat this as a concrete witness for the paper's compact-filter
  claim, not as a theorem that every unspecified boundary convention agrees with it.
- Owner decision required: none; T-0018 was already approved by
  PCD-2026-08-03-001 and PCR-2026-08-03-013.
- Evidence:
  - `IPNPCNS/Examples/OrthonormalWavelets.lean`
  - `IPNPCNS/Signal/Deterministic.lean`
  - `wotan/dev-log/T-0017.md`
  - `wotan/dev-log/T-0018.md`
  - `MODEL-OBLIGATIONS.md`
- Uncertainty:
  - Mathlib 4.31 has no packaged Hilbert--Schmidt integral-operator layer.
  - A direct all-`L²`-kernel theorem would require a substantially broader product-
    measure and kernel-approximation development than the concrete existence claim.
  - The finite-rank approximants must be connected to an actual causal integral
    representative, not merely to an abstract compact operator.
- Proposed actions:
  - Close and preserve T-0017.
  - Activate T-0018 and make the causal boundary and unit-step kernel explicit in its
    approach before implementation.
  - Prove the Volterra operator by bounded extension or an equivalent representative-
    independent `L²` construction, then establish finite-rank approximation in
    operator norm and instantiate T-0014's interfaces.
  - Record general square-integrable-kernel compactness as a follow-on only if T-0018
    demonstrates that it can be stated without hiding the boundary convention.
- Revisit when:
  - A nonzero causal convolution operator and its compactness proof compile.
  - The finite-rank approximation route exposes a missing theorem that changes the
    appropriate scope.

## PCR-2026-08-03-017

- Record type: review
- Date: 2026-08-03
- Mode: direction-review
- Trigger: T-0018 constructed the causal unit-step Volterra filter, proved its
  almost-everywhere convolution formula, norm bound, finite-rank approximation
  property, and compactness, leaving the approved Wotan queue empty.
- Control judgement: continue, operate, preserve
- Current gate: The central cone and deterministic signal claims now have concrete
  witnesses. The next exact paper-facing gap is the projection structure used before
  equation (199): reduction to `span(q)` in (195) and positive homogeneity in (196).
  The current active-face certificate proves a sufficient local formula but does not
  yet expose these two global projection laws.
- Recommendation: Create and execute T-0019. Prove positive homogeneity of metric
  projection onto every closed cone for nonnegative scalars. Prove that projection
  onto a cone with finite-dimensional span depends only on the orthogonal projection
  of the input onto that span, then specialize this to finitely generated cones. Reuse
  the existing variational characterization and keep intrinsic relative-interior face
  necessity outside this task.
- Owner decision required: none; PCD-2026-08-03-001 authorizes necessary follow-on
  work and this task closes exact deterministic equations without expanding into an
  empirical support-selection model.
- Evidence:
  - `IPNPCNS/Signal/Volterra.lean`
  - `IPNPCNS/Model/ActiveFace.lean`
  - `IPNPCNS/Cone/MetricProjection.lean`
  - `IPNPCNS/Cone/Comparison.lean`
  - `MODEL-OBLIGATIONS.md`
  - `wotan/dev-log/T-0018.md`
- Uncertainty:
  - The span-reduction theorem needs an orthogonal projection onto `span(q)`; the
    paper's finitely generated hypothesis should provide finite dimensionality, but
    the bridge from closed conic hull to real linear span must be explicit.
  - A full relative-interior partition and necessity theorem would require a larger
    polyhedral-face API and is not needed to prove (195)--(196).
- Proposed actions:
  - Add T-0019 after T-0018 and prove the general homogeneity theorem first.
  - State span reduction under an explicit finite-dimensional-span premise and derive
    the finite-generator corollary without assuming that the ambient Hilbert space is
    finite-dimensional.
  - Update the population-model obligations and revisit the remaining deterministic
    queue after the two equations compile.
- Revisit when:
  - Equations (195) and (196) compile with assumption and axiom audits.
  - The finite-generator span bridge reveals a stronger closure premise than the
    paper supplies.

## PCR-2026-08-03-018

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0019 proved equations (195) and (196), including the finite-generator
  span bridge without finite-dimensionality of the ambient Hilbert space, and the
  Wotan queue again became empty.
- Control judgement: continue, operate, preserve
- Current gate: Equation (33) still represents its `O(Δt²)` term by a supplied
  `QuadraticRemainder`. The paper's slow-input qualification suggests a concrete
  analytic theorem, but arbitrary `L²` signals do not provide the pointwise regularity
  needed to derive it.
- Recommendation: Create and execute T-0020. Define the exact one-step response of
  the first-order membrane low-pass equation as an exponentially weighted Bochner
  integral. For a nonnegative step, positive time constant, and a Lipschitz drive on
  the step interval, prove its decomposition into equation (33)'s frozen-input update
  plus an explicit remainder bounded by a constant times `Δt²`. Instantiate the
  existing `QuadraticRemainder` interface from this proof.
- Owner decision required: none; the task derives a stated deterministic
  approximation under the smallest visible regularity premise and does not assert
  that biological or arbitrary `L²` inputs satisfy it.
- Evidence:
  - `IPNPCNS/Signal/Deterministic.lean`
  - `IPNPCNS/Signal/Volterra.lean`
  - `MODEL-OBLIGATIONS.md`
  - `wotan/dev-log/T-0014.md`
  - `wotan/dev-log/T-0019.md`
  - Equation (33) and its slow-feedforward qualification in `tmp/pdfs/paper.txt`
- Uncertainty:
  - Mathlib's vector-valued interval-integral API may make the exact exponential
    kernel integral more costly than the scalar calculation.
  - A bound using `L / (2τ)` is available by discarding exponential decay; retaining a
    sharper constant is optional and should not obscure the quadratic order.
- Proposed actions:
  - Add T-0020 after T-0019 and formalize the exact low-pass step for a complete real
    normed space.
  - Prove the constant-drive integral identity and isolate the varying-drive error.
  - Bound the error from a Lipschitz hypothesis and build a concrete
    `QuadraticRemainder` witness for equation (33).
  - Preserve the existing abstract interface as the correct endpoint for signals
    without the new regularity premise.
- Revisit when:
  - The exact integral decomposition and quadratic norm bound compile.
  - Vector-valued integration reveals a missing hypothesis that changes the model
    interpretation.

## PCR-2026-08-03-019

- Record type: review
- Date: 2026-08-03
- Mode: checkpoint
- Trigger: T-0020 derived equation (33)'s quadratic remainder from the exact
  exponential low-pass step under an explicit Lipschitz-drive premise, leaving the
  Wotan queue empty.
- Control judgement: continue, operate, preserve
- Current gate: The exponential replacement following equation (30) remains an
  `ExponentialOccupancyErrorBound` premise even though the exact finite occupancy
  theorem is complete. This is the smallest remaining deterministic approximation
  with a clear quantitative endpoint.
- Recommendation: Create and execute T-0021. For `0 < n` and `p ≤ n`, put
  `x = p/n`. Use `1-x ≤ exp(-x)`, the second-order exponential remainder on
  `0 ≤ x ≤ 1`, and a finite power-difference estimate to prove that the
  exponential occupancy approximation underestimates the exact occupancy by at most
  `m p²/n`. Instantiate the existing error interface with this explicit bound.
- Owner decision required: none; the approximation and its parameter regime are
  already in project scope, and the theorem strengthens an existing visible premise
  without changing the sampling model.
- Evidence:
  - `IPNPCNS/Probability/Occupancy.lean`
  - `MODEL-OBLIGATIONS.md`
  - `wotan/dev-log/T-0013.md`
  - `wotan/dev-log/T-0020.md`
  - Equation (30) and its approximation sign in `tmp/pdfs/paper.txt`
- Uncertainty:
  - Mathlib may not package the exact finite power-difference inequality in the needed
    real interval form; a short induction should suffice.
  - The bound is intentionally elementary and may not be asymptotically sharp for
    large occupancy ratios, but it is explicit, uniform over valid parameters, and
    vanishes in the sparse regime at the expected order.
- Proposed actions:
  - Add T-0021 after T-0020.
  - Prove the local one-step exponential error and lift it through the `m`th power.
  - Translate the result to `exactOccupancyFormula`,
    `exponentialOccupancyApproximation`, and the exact expectation theorem.
  - Retain zero and invalid parameter cases as the separate theorems already present.
- Revisit when:
  - The signed and absolute occupancy-error bounds compile.
  - The power estimate exposes a parameter restriction stronger than `p ≤ n`.
