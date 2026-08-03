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
