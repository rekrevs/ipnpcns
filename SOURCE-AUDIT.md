# LaTeX Source Conformance Audit

## Purpose and verdict

This record audits the Lean development against the author-supplied LaTeX source of
*Information Processing by Neuron Populations in the Central Nervous System: A
Theory of the Mathematical Structure of Data and Operations*. The source archive,
rather than text extracted from the distributed PDF, is treated as authoritative for
formula bodies, macro expansion, cross-references, and nearby qualifications.

The audit found no material mathematical discrepancy in the claims made by the Lean
project. The signs, closure convention, domains, indices, constants, and principal
quantifiers of every claimed source result agree with the formal statements. One
non-mathematical documentation error was corrected: the wavelet module referred to
Section 5, whereas the source places the construction in Section 3.2.

The audit also records source material that the project does not claim to verify.
This distinction is essential. In particular, the Lean development does not verify
the empirical adequacy of the CNS model, a random Johnson--Lindenstrauss theorem,
general stochastic-gradient convergence, or the complete biological mechanism that
would discharge the population-level approximation assumptions.

## Source identity and reproducibility

### Supplied artifacts

| Artifact | Size | SHA-256 |
|---|---:|---|
| `arXiv-2309.02332v3.tar.gz` | 477,952 bytes | `a85f550647583374b73549e34cff596d0bd0c7991ea5586583f6cbdb068e1305` |
| `2309.02332v3.pdf` | 789,034 bytes | `fe75fb70362860e640080ccdacba96e129c4f331a0b62359e7a496fa4d2c2944` |

The archive's `00README.json` declares one top-level source,
`cns-information-processing-v19.tex`, compiled with `pdflatex` under TeX Live 2025.
The archive contains that file, `00README.json`, and twelve root-level PDF figures.
It contains no nested paths, external bibliography database, included TeX file, or
executable member. The bibliography is embedded in the top-level source.

The archive was extracted only into a temporary directory and remains untracked by
Git. Its members are:

- `00README.json`
- `cns-information-processing-v19.tex`
- `fig-1-populations-3.pdf`
- `fig-2-subspace-concepts-3.pdf`
- `fig-3-subspace-operations-2.pdf`
- `fig-4-activation-function-2.pdf`
- `fig-5-adaptive-filter-2.pdf`
- `fig-6-cone-concepts-3.pdf`
- `fig-7-cone-operations-3.pdf`
- `fig-8-moreau-double-rejection-1.pdf`
- `fig-9-primitives-by-neurons.pdf`
- `fig-10-other-operations.pdf`
- `fig-11-adaptive-filter-applications-2.pdf`
- `fig-12-sensorimotor-association.pdf`

### Independent source build and PDF comparison

Three `pdflatex` passes under the locally installed TeX Live 2026 produced a
60-page A4 PDF of 790,835 bytes with SHA-256
`4ac22723ae52a3cfc7b162252a0f83b72dc0e65700f16c07aec058befd1ea9f4`.
The final log contains no unresolved reference or citation. The remaining overfull
and underfull box notices originate in the supplied layout and do not alter content.

A layout-preserving `pdftotext` comparison gives:

| Rendering | Lines | Words | Characters |
|---|---:|---:|---:|
| Distributed arXiv PDF | 3,065 | 24,634 | 181,564 |
| Locally compiled source | 3,060 | 24,629 | 181,078 |

The unified diff has one hunk, confined to the title page. The distributed PDF adds
the arXiv identifier and consequently positions the title and author block
differently. The article body is textually identical. This establishes that the
audited source is the content source of the distributed PDF, not merely a nearby
revision.

### Macro and notation audit

The mathematical macros do not conceal substantive operations:

- `\myvec` and `\mymat` apply bold formatting only.
- `\Conic` declares the printed operator name; equation (62) supplies its meaning.
- `\polar` and `\Polar` are textual labels only.
- `\argmin`, `\tr`, `\Col`, and related commands declare operator typography.
- Cross-reference macros wrap ordinary `\ref` commands and do not alter formulas.

The source explicitly defines `Conic(c)` as the norm closure of finite nonnegative
linear combinations. It explicitly uses the non-positive polar convention
`<z,y> <= 0`. These are exactly the conventions isolated in `FORMALIZATION-SPEC.md`
and implemented by `IPNPCNS/Cone/Basic.lean`.

## Status vocabulary

The traceability tables use the following classifications.

- **Verified**: a compiled Lean theorem proves the source statement, or a stronger
  statement whose specialization is the source statement.
- **Verified with explicit premises**: the source calculation is proved after an
  informal modeling or regularity qualification has been made a named hypothesis.
- **Constructively strengthened**: the source approximation is replaced by an exact
  finite model or an explicit error theorem.
- **Represented**: the source object or assumption is encoded, but the empirical or
  analytic premise is not derived by Lean.
- **Not formalized, not claimed**: the item is background, cited mathematics,
  empirical content, or a deliberately excluded extension. It is listed to prevent
  accidental overstatement of coverage.

## Equation-by-equation traceability

### Representation and manipulation of subspaces

| Source item | Source meaning and qualifications | Lean evidence | Status |
|---|---|---|---|
| (1)--(3) | Classical neuron and population equations; support notation | No project theorem claims these biological setup equations | Not formalized, not claimed |
| (4)--(11) | Observation matrix, its column-space representation, and `Col(A)=Col(AA^T)` | `matrixColumnSpace`; `matrixColumnSpace_mul_transpose`; `columnEquivalent_mul_transpose` in `Subspace/FiniteMatrix.lean` | Verified for arbitrary finite real rectangular matrices |
| (12) | Orthogonal complement represented by `I-PP+` | `complement_starProjection`; `one_sub_matrixProjector_eq_orthogonalProjectorMatrix`; `matrixColumnSpace_one_sub_matrixProjector` | Verified intrinsically and in Moore--Penrose matrix form |
| (13) | Subspace sum represented by concatenation or `PP^T+QQ^T` | `range_linearMapSum`; `range_linearMapSum_self_comp_adjoint` | Verified |
| (14) | Sum does not distribute over intersection | `subspace_sum_not_distributive` in `Subspace/Examples.lean` | Verified by an exact two-dimensional counterexample |
| (15)--(16) | Orthogonal projection and rejection of subspaces | `subspaceProjection_eq_range_comp`; `subspaceRejection_eq_range_comp`; matrix renderings in `Subspace/MoorePenrose.lean` | Verified |
| (17)--(20) | Double subspace rejection recovers projection | `double_subspaceRejection_eq_projection`; `doubleRejection_matrix_identity`; `matrixColumnSpace_doubleRejection` | Verified intrinsically and in matrix form |
| (21)--(23) | De Morgan law and two rejection-based intersection formulas | `orthogonal_sup_eq_inf_orthogonal`; `inf_eq_orthogonal_sup_orthogonal`; `intersection_eq_sum_reject_mutualRejections`; `matrixColumnSpace_intersection_formula` | Verified |
| (24) | Frobenius pairing and trace identity | `frobeniusInner`; `frobeniusInner_eq_trace_transpose_mul` | Verified |
| (25)--(26) | Gleason representation and the normalized projector state | These are cited background and are not dependencies of the new results | Not formalized, not claimed |
| (27)--(29) | Directional overlap, orthonormal-basis sum, and symmetric projector cosine | `subspaceOverlap_eq_frobeniusInner`; `subspaceOverlap_eq_sum_norm_projection`; `directionalSubspaceMeasure_eq_average`; `symmetricSubspaceCosine_eq_frobenius` | Verified, including degenerate and range lemmas |

The Moore--Penrose development constructs the inverse from the equivalence between
the orthogonal complement of the kernel and the range. It proves all four Penrose
equations and uniqueness for arbitrary finite-dimensional real linear maps, including
zero and rank-deficient maps. The source's matrix formulas therefore do not rely on an
unrecorded full-rank assumption.

### Sparsity and collateral occupancy

| Source item | Source meaning and qualifications | Lean evidence | Status |
|---|---|---|---|
| (30), exact term | Each of `m` active axons independently chooses `p` distinct targets from `n`; `q=n(1-(1-p/n)^m)` is the expected occupied count | `expectedOccupied_eq_exactFormula` in `Probability/Occupancy.lean` | Verified from a finite uniform Cartesian-product experiment for `0<n` and `p<=n`; invalid and zero cases are separate theorems |
| (30), exponential replacement | `(1-p/n)^m` is approximated by `exp(-mp/n)` | `exponentialOccupancyApproximation_le_exactOccupancyFormula`; `expectedOccupied_exponential_sq_error` | Constructively strengthened: the approximation is a lower bound and its absolute count error is at most `m p^2/n` |
| Paragraph after (30) | Under independent, uniformly distributed messages, expected two-message overlap is approximately `q^2/n` | `TwoMessageTargetModel.expectedOverlap_eq_sq_div`; `expectedOccupiedOverlap_eq_sq_div` | Constructively strengthened: exact for the explicit independent product law; no biological independence claim is inferred |

### Signals, filtering, wavelets, and membrane dynamics

| Source item | Source meaning and qualifications | Lean evidence | Status |
|---|---|---|---|
| (31) | Fixed nonnegative weighted aggregation of inhibitory signals | `aggregateSignal`; `aggregateSignal_mem_cone` in `Signal/Deterministic.lean` | Verified in an arbitrary real normed signal space; the cone result requires the source's nonnegativity premise |
| (32) | First-order membrane transfer function in the Laplace domain | `TransferIdentity` and `TransferIdentity.apply` | Represented as an explicit operator identity; no general Laplace-transform realization is claimed |
| Finite-window signal model | Messages lie in `L2([0,T];R^n)`; spatial matrices act pointwise | `recordingMeasure`; `ScalarSignal`; `VectorSignal`; `liftMatrix`; norm bounds | Verified as Bochner `L2` over restricted Lebesgue measure |
| Compact filtering paragraph | Finite-window convolution with suitable square-integrable kernels is compact and admits finite-rank approximation | `ConvolutionHypotheses`; `HasFiniteRankApproximations`; `CompactFilterPremise`; the concrete `volterraOperator` and unit-step causal convolution in `Signal/Volterra.lean` | Verified for the explicit causal Volterra/unit-step model; generic kernel and boundary-convention claims remain explicit interfaces |
| Unnumbered wavelet dictionary | `T=0.20`, `gamma=4/sqrt(3T)`, Hann envelope, 30-Hz cosine/sine and 60-Hz cosine, zero mean, orthonormality | `wavelet_zero_mean`; `wavelet_gram`; `wavelet_orthonormal` in `Examples/OrthonormalWavelets.lean` | Verified exactly in the recording-window `L2` space |
| (33) | Low-pass update with `lambda=1-exp(-Delta t/tau_m)` and an `O(Delta t^2)` remainder, under slow weight/input variation and linear activation | `exactMembraneStep_eq_firstOrder_add_remainder`; `norm_membraneRemainderValue_le`; `exactMembraneUpdate_eq_updateWithRemainder` | Verified with explicit premises `Delta t>=0`, `tau>0`, and Lipschitz net drive; remainder norm at most `(L/tau)|Delta t|^2` |
| Wavelet/NNLS examples, including (43)--(45) | Exact unconstrained, nonnegative, and plasticity examples and residual/output signs | `example_one_*`, `example_two_*`, `example_three_*` | Verified exactly; firing-rate baseline subtraction is a separate visible convention |
| (46)--(61) | Two-channel population example, matrix update, and Gaussian subspace-learning derivation | Reusable matrix, wavelet, NNLS, and subspace-rejection components exist, but this entire example is not packaged as one theorem | Not formalized, not claimed as a complete example |

The concrete Volterra construction is causal on the finite window. The Lean module
proves that it is neither a periodic convolution nor a whole-line zero-extension
convolution under those alternative boundary definitions. This prevents a boundary
convention from being silently changed during formalization.

### Nonnegative least squares and learning

| Source item | Source meaning and qualifications | Lean evidence | Status |
|---|---|---|---|
| (34) | Classical unconstrained LMS component update | No dedicated endpoint | Not formalized, not claimed |
| (35), (38) | Componentwise nonnegative clipping is Euclidean projection, giving one projected stochastic-gradient step when `z` is the instantaneous residual | `positivePart`; `projectedUpdate`; `projectedUpdate_fixed_iff_kkt` | The finite projected step is represented exactly; stochastic convergence is not inferred |
| (36) | Finite batch NNLS objective | `nnlsPrediction`; `nnlsLoss`; `IsNNLSMinimizer` | Verified |
| (37) | Per-observation residual and loss decomposition | The same finite coordinates underlie `nnlsLoss`, but no separately named stochastic-sample object is exposed | Represented at batch level |
| (39) | Batch gradient `X(X^T w-y)` | `nnlsGradient`; `nnlsLoss_hasDerivAt_line` | Verified as the directional derivative of (36) |
| (40)--(41) | Projected fixed point iff complementary KKT; KKT iff global NNLS minimum | `projectedBatchUpdate_fixed_iff_kkt`; `nnlsMinimizer_iff_complementaryKKT`; `projectedBatchStep_fixed_iff_nnlsMinimizer` | Verified for every positive step size |
| Deterministic convergence after (41) | For `0<epsilon<2/||X||_2^2`, batch projected gradient converges; prediction is unique, coefficients are unique under injectivity | `projectedBatchIterate_tendsto_of_designSpectralBounds`; rank-deficient Fejer and convergence theorems in `NNLSRankDeficient.lean` | Verified under explicit upper/lower spectral bounds; rank-deficient convergence to some minimizer is also proved |
| Stochastic paragraph after (41) | Convergence under unbiased sampling, moment bounds, Robbins--Monro steps; constant-step tracking qualification | No filtration or probability-process development | Not formalized, not claimed |
| (42) | Hilbert-space signal objective with finite coefficient vector and inner-product gradient | The finite-coefficient geometry and concrete wavelet instances are verified, but no general theorem with arbitrary Hilbert-valued columns is exposed | Not formalized as a separate endpoint |

For `lambda<1`, the source itself states that the update is an exact gradient only
after identifying a matched filtered objective. The Lean project preserves that
qualification and does not identify the transient membrane update with an unfiltered
NNLS gradient.

### Closed-cone foundations and operations

| Source item | Source meaning and qualifications | Lean evidence | Status |
|---|---|---|---|
| (62) | Norm-closed conic hull of an arbitrary set | `conicHull`; `subset_conicHull`; `conicHull_le` | Verified |
| (63) | Cone represented by a finite frame | `finiteGeneratedCone`; finite-span and finite-dimensionality theorems in `Model/ActiveFace.lean` | Represented and verified at the closed-hull level; redundancy of closure for every finite frame is not a separate endpoint |
| (64) | Intrinsic definition of a face | The project uses selected finite-generator active certificates rather than a general intrinsic face type | Not formalized, not claimed |
| (65) | Unique metric projection on a closed convex cone | `metricProjection`; membership and minimality theorems | Verified for arbitrary real Hilbert spaces |
| (66) | Non-positive polar | `polar`; `mem_polar`; antitonicity and bipolar theorems | Verified with the source sign convention |
| (67)--(71) | Moreau decomposition, uniqueness, variational and cone-polar characterizations, residual identity | `moreau_add`; `moreau_inner`; `moreau_unique`; `metricProjection_inner_le_zero`; `metricProjection_eq_iff`; `metricProjection_polar_eq_sub` | Verified |
| (72) | Closed Minkowski sum | `sumSet`; `coneSum`; its order and membership lemmas | Verified using the source's closed-hull convention; the alternate `Conic(a union b)` display is not a separate theorem |
| (73)--(74) | Closed conic projection and rejection, including the residual-generator representation | `projectedSet`; `coneProjection`; `coneRejection`; `coneRejection_eq_residualHull` | Verified |
| (75) | Projection by double rejection | `doubleRejection` | Verified; duplicated as headline equations (98)/(108) |
| (76)--(79) | Intersection and its three rejection/sum renderings | `inf_eq_left_rejection`; `inf_eq_right_rejection`; `inf_eq_sum_rejection`; `intersectionByRejections` | Verified |
| (80) | Reflection through the origin | `coneReflection`; membership, monotonicity, involution, polar, projection, and sum equivariance lemmas | Verified |
| (81) | `span(a)=a+(-a)` | `coneSpan` represents the left side and reflection/sum machinery represents the right side, but no dedicated equality theorem is exposed | Not formalized as a separate endpoint |
| (82)--(86) | Numerical two-message cone example and residual sign | Its general Moreau/rejection mechanism is verified, but the complete numerical example is not packaged | Not formalized, not claimed as a complete example |

Although finite generation is the paper's default representation convention, the
headline cone theorems explicitly state that they hold for arbitrary closed convex
cones. The Lean core follows this broader source quantification and therefore does
not add finite-dimensional or polyhedral assumptions to those results.

### Cone comparison and exact cone algebra

| Source item | Source meaning and qualifications | Lean evidence | Status |
|---|---|---|---|
| Inclusion test before (87) | `A` is contained in `B` iff `A` rejected by `B` is the zero cone | `coneRejection_eq_bot_iff_le`; `cone_eq_iff_mutual_rejection_bot` | Verified |
| (87)--(89) | Unit directions, symmetric worst-case similarity, and angle | `unitDirections`; `directionalConeSimilarity`; `coneSimilarity`; `coneAngle` and range/edge-case theorems | Verified for nonzero cones, exactly matching the source's separate empty-cone treatment |
| (90)--(92) | Normalized finite-frame proxy and its optimistic error bound under two-sided `gamma` coverage | `ConeFrame.normalized`; `frameConeSimilarity`; `FrameCoverage`; `frameConeSimilarity_error92` | Verified with finite nonempty frames and explicit coverage |
| (93)--(97) | Projection containment, polarity order reversal, bipolarity, absorption, and polar-sum intersection law | `coneProjection_subset_right`; `le_iff_polar_ge`; `eq_polar_polar`; `coneProjection_absorb`; `inf_eq_polar_coneSum_polar` | Verified |
| (98)--(108) | Pointwise and closed-hull proof that double rejection equals conic projection | `metricProjection_polar_rejection_eq`; `doubleRejection` | Verified for arbitrary closed convex cones in arbitrary real Hilbert spaces |
| (109)--(157) | Full intersection proof and all three final rejection formulas | The helper theorems and `intersectionByRejections` in `Cone/Intersection.lean` | Verified for arbitrary closed convex cones, including closure-safe sums |

The source proof uses `r=a reject b`, the inclusion `r subset polar(b)`, bipolarity,
and pointwise Moreau uniqueness before taking closed conic hulls. The Lean proof has
the same architecture. It does not identify a pointwise image with a closed hull
without a separate extensional argument.

### Exact and approximate transmission invariance

| Source item | Source meaning and qualifications | Lean evidence | Status |
|---|---|---|---|
| (158)--(160) | Linear cone image; exact sum/reflection equivariance for finite cones; exact restricted conformality benchmark | No source-shaped endpoint for this complete exact benchmark | Not formalized, not claimed |
| (161) | Scaled near-isometry on a relevant set or subspace | `ScaledNearIsometryOn` | Represented exactly |
| (162) | Near-isometry on a subspace implies inner-product distortion by polarization | `scaledInnerDistortionOn_of_scaledNearIsometryOn_submodule` | Verified with the sharp source constant |
| (163) | Angular margin preserves the sign of an inner product | `inner_map_pos_of_margin`; `inner_map_neg_of_margin` | Verified |
| (164)--(167) | A transformed-space projection preimage satisfies the distance-ratio, Pythagorean, and projection-error bounds | `distance_ratio_of_scaledNearIsometryOn`; `projection_pythagorean_lower`; `projection_error_of_scaledNearIsometryOn` | Verified with explicit premises that the relevant residuals satisfy (161), that `q` is feasible, and that it has transformed-space optimality. The source's separate existence/closed-image argument and the final transmitted-space norm corollary are not packaged as endpoints |
| (168) | Johnson--Lindenstrauss dimension order and probability qualification | External cited probability theorem | Not formalized, not claimed |
| (169) | Disjoint equal-gain columns give `M^T M=alpha I` | No dedicated endpoint | Not formalized, not claimed |
| (170)--(171) | Column gain/coherence assumptions imply the sharp active Gram/RIP bound `eta+(k-1)mu` | `ColumnBounds170`; `activeGramRIP171`; `sparseGramRIP171_of_card_le` | Verified deterministically in an arbitrary real inner-product target space |
| (172) | Equal branches with at most `r` shared targets give `mu<=r/d` and the corresponding distortion | No combinatorial branch-incidence endpoint | Not formalized, not claimed |
| (173) | Full spatiotemporal branch/filter operator | Finite spatial lifting and temporal-filter interfaces exist, but this heterogeneous path formula is not instantiated | Not formalized, not claimed |

The source requires the near-isometry model to cover every intermediate vector used
by a cone calculation, not merely observed frame rays. The Lean theorem reflects this
by requiring membership of both residual vectors used in (165); it never infers
coverage from frame membership alone.

### Population realization and circuits

| Source item | Source meaning and qualifications | Lean evidence | Status |
|---|---|---|---|
| (174)--(176) | Error/output sign convention and ideal population primitive `-(p reject q)` | `populationPrimitive` | Equation (176) verified as the exact ideal cone-level definition; (174)--(175) are motivating sign conventions |
| (177)--(183) | Population NNLS optimum, Moreau residual, and expectation argument | Finite NNLS and Moreau theorems verify reusable mathematical components; no biological population/training probability model discharges these assumptions | Not formalized as a complete population theorem |
| (184)--(194) | Sparse ray training pairs, learned correspondences, selected supports, and ideal Moreau reconstruction | These are the source's learning and data assumptions. `PopulationRegion` begins after such a map and support have been selected | Represented only through later interfaces; not derived |
| (195) | Cone projection depends only on the component in the cone span | `metricProjection_starProjection_eq`; `metricProjection_finiteGeneratedCone_span` | Verified, including finite cones in infinite-dimensional ambient Hilbert spaces |
| (196) | Positive homogeneity of cone projection | `metricProjection_smul` | Verified for every closed cone and nonnegative scalar |
| (197)--(200) | Intrinsic face regions, relative interiors, local span projector, and its matrix rendering | `ActiveFaceCertificate`; `activeFaceRegion`; `selectedFaceProjection`; `metricProjection_finiteGeneratedCone_eq_selectedFaceProjection` | Equation (199) is constructively verified from sufficient finite KKT/Moreau inequalities. Necessity, intrinsic face/relative-interior partitioning, and the matrix inverse display (200) are not claimed |
| (201)--(203) | Support-selected population map and ideal exact reconstruction | `PopulationRegion.populationMap` and `PopulationRegion.ofFiniteActiveFace` expose the map and certified region | Represented; the learned equality is not derived from biological training dynamics |
| (204)--(205) | Restricted learned approximation assumption and full support-selected map | `PopulationRegion.Approximation204` | Equation (204) is deliberately an explicit assumption, not a theorem about biology or training |
| (206)--(207) | Projection and residual error consequences of (199) and (204) | `PopulationRegion.projection_error206`; `PopulationRegion.residual_error207` | Verified with explicit domain membership |
| (208) | Exact source-wide maps generate the exact conic projection and rejection hulls | `exact_population_hulls`; `PopulationRegion.exact_hulls_of_zero` | Verified under exact coverage/equality premises |
| (209) | Reflection commutes with rejection | `coneReflection_rejection` | Verified |
| Figure 9 projection/intersection circuits | Realization using population primitives, reflection, and sum | `coneProjection_eq_populationCircuit`; `inf_eq_populationCircuit` | Verified algebraically |
| (210) | Cone-valued conditional controlled by whether a cone is zero | `EmptinessControlPremise`; `StrongBlockingPremise`; `controlledConditional210` | Verified with explicit synchronized control and strong-blocking premises; no emptiness detector or inhibitory dynamics is invented |

The source explicitly places stability and dynamics of the recurrent network outside
the paper's scope. The Lean project does the same. Memory, adaptive-filter
applications, and cognitive interpretations after equation (210) are circuit-level or
interpretive prose rather than additional proved mathematical identities.

## Discrepancy register

### Corrected finding

| Severity | Finding | Resolution |
|---|---|---|
| Documentation only | `IPNPCNS/Examples/OrthonormalWavelets.lean` said that the wavelets occur in Section 5 | Corrected to Section 3.2, matching the source heading and surrounding text |
| Documentation completeness | The transmission-invariance boundaries around (158)--(173) were not collected in `MODEL-OBLIGATIONS.md` | Added an explicit boundary section distinguishing the proved deterministic inequalities from exact-equivariance, existence, probability, and anatomical specializations |

### Material findings

None. No source formula, qualification, or quantifier requires a change to a Lean
definition or theorem.

### Scope observations, not discrepancies

The table deliberately identifies several source results without dedicated Lean
endpoints: Gleason's theorem, general Laplace and convolution theory, stochastic
projected-gradient convergence, exact transmission equivariance, the
Johnson--Lindenstrauss theorem, the branch-incidence example, intrinsic polyhedral
face partitions, and biological learning/support selection. These were already
outside the project's stated theorem scope or represented as explicit interfaces.
They do not invalidate any formal theorem. They must nevertheless remain visible in
both final reports so that "verified model" is never read as "verified empirical
description of the CNS" or "line-by-line formalization of every cited result."

## Audit conclusion

The LaTeX archive confirms the interpretation used by the formalization. In
particular:

1. closed conic hulls use norm-topological closure;
2. the polar uses the non-positive inner-product convention;
3. the headline double-rejection and intersection results quantify over arbitrary
   closed convex cones, not merely finite cones;
4. the occupancy overlap depends on an independence approximation;
5. the membrane remainder requires slow variation made precise in Lean by a
   Lipschitz premise;
6. deterministic NNLS and stochastic learning are distinct claims;
7. equation (204), support selection, condition control, and biological realization
   remain explicit model premises; and
8. recurrent-network stability is outside both the source's and the Lean project's
   theorem scope.

### Final verification gates

- `lake build` completed all 2,960 jobs successfully after the audit corrections.
- A source scan found no `sorry`, custom `axiom`, or `unsafe` declaration in the
  project Lean files.
- `#print axioms` was run on 38 representative public endpoints spanning subspaces,
  cones, approximation, NNLS, signals, wavelets, population realization, circuits,
  and probability. Every endpoint reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- `wotan/backlog.json` parses as valid JSON, the corrected section-reference scan is
  clean, and `git diff --check` reports no whitespace error.

The source-conformance gate is therefore passed without corrective proof work.
