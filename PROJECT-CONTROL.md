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
