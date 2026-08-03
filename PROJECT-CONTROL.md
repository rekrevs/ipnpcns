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
