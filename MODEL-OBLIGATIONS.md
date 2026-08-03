# Model and Learning Obligations

This file records paper claims that require additional mathematical or empirical input.
They are not admitted as hidden axioms in the Lean development.

## NNLS and learning

The finite batch objective, gradient, nonnegative projected update, fixed-point
equivalence, global KKT optimality, and deterministic convergence under an explicit
spectral contraction are represented in `IPNPCNS/Learning/NNLS.lean`,
`IPNPCNS/Learning/NNLSOptimality.lean`, and
`IPNPCNS/Learning/NNLSConvergence.lean`.

The following claims require separate theorem packages:

- derivation of the implemented strict contraction from singular-value bounds and a
  familiar step interval such as `0 < ε < 2 / ‖X‖²` in the full-row-rank case;
- a rank-deficient convergence theorem to the minimizer set rather than to a unique
  coefficient vector;
- stochastic projected-gradient convergence under a specified filtration, unbiased
  sampling law, moment bounds, and Robbins–Monro step-size conditions;
- a steady-state tracking or misadjustment theorem for constant step size;
- identification of the `λ < 1` update with the gradient of a matched filtered
  objective.

The phrase “under standard assumptions” is a research pointer, not a proposition.

## Face and support selection

`IPNPCNS/Model/Population.lean` represents one active face/support region. Its
`projection_eq_face` field isolates equation (199), while `Approximation204`
isolates the learned approximation assumption in equation (204).

A constructive sufficient active-region account is now provided in
`IPNPCNS/Model/ActiveFace.lean`. It proves equation (199) from a finite-generator
KKT/Moreau certificate and handles the empty face and overlapping boundary
certificates. A more intrinsic or empirical account still requires:

- polyhedral faces and relative interiors for finitely generated cones;
- a necessity theorem identifying the certificate region with an intrinsic
  relative-interior face partition;
- a model connecting threshold dynamics and support masks to face-region selection;
- training-data and adaptation hypotheses that imply a numerical value of `ε`.

The present theorems verify equations (206)–(208) from those explicit premises.

## Empirical boundary

Lean does not establish that biological neuron populations satisfy the model
interfaces. Anatomical connectivity, time-scale separation, convergence in vivo,
support selection, and error magnitudes require empirical evidence or certified data
linked through a separate validation model.
