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

## Deterministic signals and filters

`IPNPCNS/Signal/Deterministic.lean` fixes the signal domain used in Sections 3.1--3.3
as Bochner `L²` over Lebesgue measure restricted to `[0, T]`. It provides scalar and
finite-vector signal types, lifts finite spatial matrices pointwise, and represents
temporal filters as bounded linear operators. Equation (31), operator-norm bounds,
nonnegative conic aggregation, cone preservation, finite-dictionary spans, and the
first-order stability part of equation (33) are verified from explicit hypotheses.

The following analytic claims remain deliberately conditional:

- identifying a bounded operator with a concrete truncated convolution requires a
  selected boundary convention and an almost-everywhere integral identity;
- square-integrability of a particular impulse response and compactness of the
  resulting operator require concrete kernel regularity and domain proofs;
- compactness does not by itself become a finite-rank approximation theorem in this
  development; the required operator-norm approximation property is named
  `HasFiniteRankApproximations`;
- equation (32) requires a concrete transform and gain satisfying the named
  `TransferIdentity` premise;
- the `O(Δt²)` in equation (33) is an explicit `QuadraticRemainder`, not a conclusion
  about the biological dynamics without differentiability and time-scale premises.

The finite wavelet dictionary and its claimed orthonormality can be verified as a
separate exact example; they are not needed for the abstract deterministic layer.

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
