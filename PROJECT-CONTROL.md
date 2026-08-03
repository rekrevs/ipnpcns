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
