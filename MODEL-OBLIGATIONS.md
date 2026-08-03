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

## Exact cone circuits and conditionals

`IPNPCNS/Cone/Laws.lean` verifies equations (93)--(97), defines closed-cone
reflection, and proves the reflection/rejection law (209).  In particular, reflection
is implemented mathematically as pullback along the isometric map `x \mapsto -x`, so
it preserves both closedness and the paper's non-positive polar convention.

`IPNPCNS/Model/Circuits.lean` defines the ideal population primitive from (176) and
proves the projection and intersection circuit expansions in Figure 9.  Its theorem
for (210) is conditional on two explicit propositions: the control is inactive exactly
when the condition cone is zero, and strong inhibition passes or blocks the signal as
specified.  Lean does not supply a biological emptiness detector, synchronization
mechanism, or inhibitory dynamics from those propositions.

## Cone comparison and finite frames

`IPNPCNS/Cone/Comparison.lean` verifies the inclusion-by-empty-rejection test and
equations (87)--(92). Exact similarity is an infimum over nonzero unit directions;
its range, identity, polar-zero, and angular consequences require both cones to be
nonzero. Finite frames are represented by nonempty finite index types whose raw rays
are nonzero cone members, and normalization is proved rather than assumed.

The finite proxy is always optimistic. Its `γ` error theorem requires a named
`FrameCoverage` premise in both directions. The development does not infer that a
learned or sampled biological frame has such coverage, and states no uniform proxy
guarantee without it.

## Finite collateral occupancy

`IPNPCNS/Probability/Occupancy.lean` gives equation (30) an exact finite experiment.
Each active axon is averaged uniformly over all `p`-element subsets of `Fin n`, and
the `m` selections are averaged over their Cartesian product. The expected occupied
count is proved to be `n * (1 - (1 - p / n)^m)` for `0 < n` and `p ≤ n`; zero and
invalid parameter cases are separate theorems.

The exponential replacement has a named `ExponentialOccupancyErrorBound` premise;
no asymptotic error is silently assumed. The `q² / n` two-message overlap follows
only from separately supplied uniform-marginal and targetwise-independence premises.
Those premises remain modeling approximations, not consequences about biological
messages.

## Empirical boundary

Lean does not establish that biological neuron populations satisfy the model
interfaces. Anatomical connectivity, time-scale separation, convergence in vivo,
support selection, and error magnitudes require empirical evidence or certified data
linked through a separate validation model.
