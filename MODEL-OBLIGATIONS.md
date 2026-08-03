# Model and Learning Obligations

This file records paper claims that require additional mathematical or empirical input.
They are not admitted as hidden axioms in the Lean development.

## Finite subspaces and matrix representations

`IPNPCNS/Subspace/Basic.lean`, `FiniteMatrix.lean`, `Comparison.lean`, and
`Examples.lean` verify the intrinsic operations in equations (12)--(23), the range
identity `Col(A Aᵀ) = Col(A)`, and the trace/Frobenius comparisons (24), (27)--(29).

Mathlib 4.31 has no general Moore--Penrose matrix API. The exact `A A⁺` spelling of
the canonical projector is therefore scheduled as T-0015 rather than assumed. This
does not affect the verified subspaces or their orthogonal projectors; it only leaves
one finite matrix representation theorem package open.

## NNLS and learning

The finite batch objective, gradient, nonnegative projected update, fixed-point
equivalence, global KKT optimality, and deterministic convergence under an explicit
spectral contraction are represented in `IPNPCNS/Learning/NNLS.lean`,
`IPNPCNS/Learning/NNLSOptimality.lean`, and
`IPNPCNS/Learning/NNLSConvergence.lean`.

The following claims require separate theorem packages:

- a rank-deficient convergence theorem to the minimizer set rather than to a unique
  coefficient vector (scheduled as T-0016); strict coefficient contraction and
  full-row-rank convergence for `0 < ε < 2 / L` are proved in
  `IPNPCNS/Learning/NNLSSpectral.lean`;
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
