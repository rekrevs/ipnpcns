# Model and Learning Obligations

This file records paper claims that require additional mathematical or empirical input.
They are not admitted as hidden axioms in the Lean development.

## NNLS and learning

The finite batch objective, its stated gradient formula, nonnegative projected update,
and fixed-point/complementarity equivalence are represented in
`IPNPCNS/Learning/NNLS.lean`.

The following claims require separate theorem packages:

- KKT necessity and sufficiency for the convex NNLS objective;
- convergence of the deterministic projected-gradient iteration for
  `0 < ε < 2 / ‖X‖²`;
- uniqueness when the relevant design map has full rank;
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

A more constructive account still requires:

- polyhedral faces and relative interiors for finitely generated cones;
- a proof that cone projection equals projection onto the active face span throughout
  the stated region;
- a model connecting threshold dynamics and support masks to face-region selection;
- training-data and adaptation hypotheses that imply a numerical value of `ε`.

The present theorems verify equations (206)–(208) from those explicit premises.

## Empirical boundary

Lean does not establish that biological neuron populations satisfy the model
interfaces. Anatomical connectivity, time-scale separation, convergence in vivo,
support selection, and error magnitudes require empirical evidence or certified data
linked through a separate validation model.
