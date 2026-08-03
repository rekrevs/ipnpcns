# Model and Learning Obligations

This file records paper claims that require additional mathematical or empirical input.
They are not admitted as hidden axioms in the Lean development.

## Finite subspaces and matrix representations

`IPNPCNS/Subspace/Basic.lean`, `FiniteMatrix.lean`, `Comparison.lean`, `Examples.lean`,
and `MoorePenrose.lean` verify the intrinsic operations in equations (12)--(23), the
range identity `Col(A Aᵀ) = Col(A)`, and the trace/Frobenius comparisons (24),
(27)--(29).

Because mathlib 4.31 has no bundled general Moore--Penrose matrix API, the project
constructs one from the linear equivalence between `ker(A)ᗮ` and `range(A)`. The
construction is valid for arbitrary finite rectangular real matrices, including zero
and rank-deficient matrices. All four Penrose equations and uniqueness are proved.
The products `A A⁺` and `A⁺ A` are identified with the orthogonal projectors onto the
column and row spaces, respectively, and the matrix renderings of equations (12),
(15)--(20), and (22) are connected to the intrinsic T-0009 theorems.

## Deterministic signals and filters

`IPNPCNS/Signal/Deterministic.lean` fixes the signal domain used in Sections 3.1--3.3
as Bochner `L²` over Lebesgue measure restricted to `[0, T]`. It provides scalar and
finite-vector signal types, lifts finite spatial matrices pointwise, and represents
temporal filters as bounded linear operators. Equation (31), operator-norm bounds,
nonnegative conic aggregation, cone preservation, finite-dictionary spans, and the
first-order stability part of equation (33) are verified from explicit hypotheses.

`IPNPCNS/Signal/Volterra.lean` discharges these analytic obligations for one explicit
nontrivial model: the causal unit-step impulse response with causal truncation.  It
constructs the prefix-integration operator on scalar `L²`, proves the almost-everywhere
integral identity and the bound `‖V‖ ≤ T` for `0 ≤ T`, obtains operator-norm
finite-rank approximants from simple `L²` kernels, and proves compactness.  It also
inhabits `ConvolutionHypotheses`, `HasFiniteRankApproximations`, and
`CompactFilterPremise` with those proofs.  Periodic and whole-line zero-extension
operators are explicitly not identified with this causal construction.

`IPNPCNS/Signal/Membrane.lean` gives equation (33)'s remainder a concrete source. It
defines the exact exponentially weighted first-order low-pass step, proves that the
kernel integrates to `λ = 1 - exp(-Δt/τ)`, and recovers the displayed frozen-input
update exactly for constant drive. If the net excitation-minus-inhibition drive is
`L`-Lipschitz on a nonnegative step and `0 < τ`, the remaining Bochner integral
constructs a `QuadraticRemainder` with norm at most `(L/τ)|Δt|²`.

The following broader analytic claims remain deliberately conditional:

- identifying an arbitrary bounded operator with another truncated convolution still
  requires a selected boundary convention and an almost-everywhere integral identity;
- square-integrability and compactness for impulse responses beyond the verified
  unit-step example still require concrete kernel regularity and domain proofs;
- compactness does not by itself become a finite-rank approximation theorem in this
  development; the required operator-norm approximation property is named
  `HasFiniteRankApproximations`;
- equation (32) requires a concrete transform and gain satisfying the named
  `TransferIdentity` premise;
- equation (33)'s derived quadratic bound requires the explicit Lipschitz-drive
  premise; arbitrary recording-window `L²` signals and biological dynamics do not
  acquire that pointwise regularity automatically.

`IPNPCNS/Examples/OrthonormalWavelets.lean` now verifies the paper's separate exact
example. It uses the stated `T = 0.20 s` window, zero-extended `sin²(πt/T)` envelope,
30-Hz cosine and sine carriers, 60-Hz cosine carrier, and normalization
`4 / sqrt(3T)`. The resulting `L²` wavelets have zero mean and identity Gram matrix.
The three coordinate/NNLS examples, unique optimal coefficients, signed residuals,
and neuronal-output signs are proved exactly. Literal firing-rate baselines remain a
separate pointwise convention and are subtracted before the `L²` calculations; the
formalization does not claim that arbitrary baseline/amplitude choices give
nonnegative literal rates.

## NNLS and learning

The finite batch objective, gradient, nonnegative projected update, fixed-point
equivalence, global KKT optimality, and deterministic convergence are represented in
`IPNPCNS/Learning/NNLS.lean`, `IPNPCNS/Learning/NNLSOptimality.lean`,
`IPNPCNS/Learning/NNLSConvergence.lean`, `IPNPCNS/Learning/NNLSSpectral.lean`, and
`IPNPCNS/Learning/NNLSRankDeficient.lean`.

The rank-deficient theorem assumes only a positive upper spectral bound, the open
step interval `0 < ε < 2 / L`, and a nonempty NNLS solution set. It proves Fejér
descent, vanishing prediction error, finite-dimensional convergence to a selected
coefficient minimizer, asymptotic regularity, and equality of all minimizer
predictions. Coefficient uniqueness remains conditional on injectivity of the
prediction map; it is not inferred in kernel directions.

The following claims require separate theorem packages:

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
certificates. `IPNPCNS/Cone/ProjectionStructure.lean` additionally proves the global
laws preceding that local account: equation (196), positive homogeneity of projection
onto every closed cone, and equation (195), reduction to orthogonal projection into
the cone span. For a finitely generated cone, `ActiveFace.lean` proves that its real
span equals the span of its generators and is finite-dimensional even when the
ambient Hilbert space is not.

A more intrinsic or empirical account still requires:

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
