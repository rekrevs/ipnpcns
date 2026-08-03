# Lean Formalization Feasibility Assessment

**Date:** 2026-08-03
**Source:** `2309.02332v3.pdf` (60 pages)
**Tested environment:** Lean 4.31.0, Lake 5.0.0, and mathlib 4.31.0

## Executive judgment

It is realistic to formalize and mechanically verify the paper's deterministic
mathematical core, especially the algebra of closed convex cones in Section 4.
It is not realistic to use Lean to verify that the model is a true or biologically
adequate description of the central nervous system. Lean can prove consequences of a
precise model and explicit assumptions; empirical validity requires data and model
validation.

The recommendation is therefore a **conditional go** for a bounded pilot, not an
immediate commitment to formalize the whole paper:

1. formalize closed convex cones, the polar cone, and metric projection;
2. derive Moreau decomposition in the paper's conventions;
3. verify the double conic rejection identity, equations (98)/(108);
4. use the result to re-estimate the cost and risk of the intersection proof (109).

This pilot should take approximately **4–8 person-weeks** for someone already fluent
in Lean and mathlib. The estimate has roughly a factor-of-two uncertainty.

## What verification would establish

Three different goals must be kept separate.

| Goal | Can Lean decide it? | Comment |
|---|---:|---|
| The definitions are coherent and the theorems follow logically from explicit assumptions | Yes | This is the natural formalization target. |
| The neuron and population model realizes the cone operations under idealized learning, coding, and sparsity hypotheses | Yes, conditionally | The conclusion can be verified once the hypotheses are explicit. |
| Real neural populations satisfy the hypotheses and the model explains the CNS | No | This is empirical. Lean could at most check a separate formal bridge from certified measurements to assumptions. |

The distinction is especially clear in Section 5. Equation (204) assumes an
approximation guarantee for the learned, support-dependent population map. Equations
(206)–(208) are plausible formal consequences of that assumption; equation (204) is
not derived from a complete biological dynamics model.

## Inventory and difficulty

The scale below concerns a faithful, maintainable, mathlib-based formalization rather
than a one-off encoding of a special case.

| Paper section | Main objects or results | Assessment | Principal risk |
|---|---|---:|---|
| 2.1–2.4, subspaces | subspaces, sum, intersection, orthogonal projection/rejection, trace and Frobenius comparisons | Medium | Subspace geometry exists, but the paper's matrix formulas use the Moore–Penrose pseudoinverse, for which no ready general mathlib API was found. |
| 2.5, sparsity | occupancy probability and overlap | Low–medium | The exact expectation is straightforward; the stated overlap formula is explicitly an independence approximation and must remain labelled as such. |
| 3.1–3.3, signals | `L²([0,T]; ℝⁿ)`, convolution, filters, wavelet dictionaries, and compact operators | High | Correct signal types, boundary conditions, measurability, integrability, and regularity. The `O(Δt²)` claim needs precise smoothness hypotheses. |
| 3.4–3.5, NNLS | projected LMS/gradient method, fixed points/KKT, deterministic and stochastic convergence | Medium–very high | Finite algebraic parts are feasible. KKT lacks a ready core theory, and stochastic convergence is stated only “under standard assumptions.” |
| 4.1–4.5, exact cone algebra | closed conic hull, polar, Moreau, projection/rejection, double rejection (98), intersection (109) | Medium–high | Best pilot area. The foundations exist, but the notation, polar sign, topological closure, and reusable projection API must be built. |
| 4.6, approximate invariance | subspace embedding/RIP, projection error (167), rectangular maps, Gershgorin bound (171) | Medium for deterministic parts; high for random parts | Gershgorin exists in mathlib. No ready Johnson–Lindenstrauss/RIP endpoint was found; the probability result would be a project of its own or an explicit external hypothesis. |
| 5.1–5.3, population realization | NNLS correspondence, face regions, piecewise-linear projection (199), support masks, error assumption (204) | High | Requires polyhedral cones, faces/relative interior, and a piecewise-linearity proof. Biological connectivity and learning assumptions must be separated from derived theorems. |
| 5.4–5.7, circuits and interpretation | composition of primitive populations into cone operations and conditionals | Medium after the core | The algebraic wiring schemes can be verified, but stability of recurrent circuits is stated to be outside the paper's scope. |

Gleason's theorem and several signal-processing results are mainly motivational or
cited background. They are not dependencies of the new cone identities. A “formalize
every cited theorem” interpretation would multiply the project size.

## Audit of the main proofs

The two new headline results in Section 4.5 were checked both in extracted text and on
rendered PDF pages.

### Double rejection, (98)/(108)

The proof strategy is structurally sound:

- Moreau decomposes `x ∈ a` into `P_b x + P_{¬b} x`;
- the residual belongs to `r = a ¬ b`, and `r ⊆ ¬b` gives `b ⊆ ¬r` by polarity
  and bipolarity;
- the same orthogonal decomposition is therefore identified as the Moreau
  decomposition relative to `¬r`;
- the pointwise equality is lifted to equality of closed conic hulls.

This is a good first target: substantial enough to exercise the architecture, but free
of probability, matrix computation, and biological assumptions.

### Intersection, (109)/(155)–(157)

The longer proof is also coherent under manual review. Its Lean cost will mostly be
bookkeeping for four Moreau decompositions, polarity inclusions, orthogonality, and the
passage from pointwise projections to closed conic hulls. It should be attempted only
after the pilot has produced stable helper lemmas. There is a larger risk of lengthy,
brittle term manipulation, but no evident mathematical blocker was found.

A manual audit is not a correctness proof. The absence of an obvious paper error is a
reason to run the pilot, not a reason to skip it.

## Current mathlib support and compiled probe

Current mathlib provides an unusually good starting point:

- `ProperCone ℝ H` represents the closed convex cones needed by the core;
- `PointedCone.hull`, closure, continuous linear maps, and dual cones exist;
- the Hilbert projection theorem gives a nearest point in a nonempty complete convex
  set;
- a variational characterization of minimizers corresponds to equation (69);
- dual/double-dual results, finite conic generation, finite-dimensional singular values,
  `L²`, convolution, compact operators, and Gershgorin's theorem are available as
  building blocks.

A local Lean probe imported these modules and, for an arbitrary real Hilbert space and
`C : ProperCone ℝ H`, defined a `noncomputable` metric projection with membership
and minimality theorems. This check exited successfully:

```text
lake env lean /private/tmp/ipnpcns-probe.lean
```

This demonstrates that the first critical type/library bridge compiles. It does not
prove Moreau decomposition or either of the paper's new identities.

Source inspection found no bundled general metric-projection API for convex sets, no
cone Moreau decomposition, and no Hilbert–Schmidt theory. Mathlib's nonsingular matrix
inverse module explicitly says that it does not treat pseudoinverses. KKT remains a
TODO. These gaps are tractable, but they are genuine library development rather than
mere transcription.

Relevant official mathlib documentation:

- [Hilbert projection theorem and projection criterion](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Minimal.html)
- [Closed convex cones (`ProperCone`)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Cone/Basic.html)
- [Dual cones and the double dual](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Cone/Dual.html)
- [Conic hull](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Convex/Cone/Pointed.html)
- [Finite-dimensional singular values](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/SingularValues.html)
- [`L²`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/L2Space.html), [convolution](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convolution.html), and [compact operators](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Operator/Compact/Basic.html)
- [Gershgorin circle theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Gershgorin.html)

## Points requiring clarification before full formalization

1. **Closure.** `Conic`, sums, and mapped images must consistently use norm-topological
   closure. The paper states this convention, but individual displayed formulas look
   purely algebraic if the qualification is lost.
2. **Polar sign.** The paper uses `⟨z,y⟩ ≤ 0`; mathlib's dual cone uses
   `0 ≤ ⟨y,z⟩`. Define the polar as a reflected dual and prove explicit bridge lemmas.
3. **General versus finite cones.** Section 4.5 concerns closed convex cones in Hilbert
   space; the neural representation uses finitely generated cones. These levels should
   have separate types or hypotheses.
4. **Pseudoinverse.** Either develop Moore–Penrose theory for the paper's matrix
   formulas, or first prove coordinate-free results using orthogonal projection and
   postpone the matrix statements to corollaries.
5. **Analytic hypotheses.** Convolution, compactness, discretization error, and filter
   results need domains, regularity, and boundary conditions that are not always stated
   theorem-by-theorem.
6. **Optimization hypotheses.** Step size, existence/uniqueness, stochastic model,
   independence or martingale conditions, and moment bounds for LMS/SGD must be
   explicit. “Standard assumptions” cannot be formalized.
7. **Random embeddings.** Deterministic consequences of an RIP/embedding assumption
   can be verified directly. Initially treat the Johnson–Lindenstrauss probability
   guarantee as an imported theorem or hypothesis to preserve focus.
8. **Population model.** Coding alignment, support selection, training coverage, and
   equation (204) must be assumptions in a separate model interface. They must not be
   hidden inside a definition saying that a neuron “implements projection.”
9. **Numerical examples.** Floating-point simulations are validation, not proofs. Small
   examples can instead be exact or use certified error intervals.

## Recommended Lean architecture

General mathematics should remain independent of its biological interpretation:

```text
Cone.Basic             closed cones, closed conic hull, polar/reflection
Cone.MetricProjection  chosen projection, uniqueness, variational criterion
Cone.Moreau            Moreau, residual, and bipolarity bridges
Cone.Operations        sum, conic projection, and rejection
Cone.DoubleRejection   (98)/(108)
Cone.Intersection      (109)/(155)–(157)
Approx.Invariance      (161)–(167), followed later by RIP/Gershgorin
Finite.Subspace        coordinate-free subspace results, then matrices/pseudoinverse
Learning.NNLS          separate finite-dimensional optimization layer
Model.Population       assumption bundles and conditional realization theorems
```

Build the coordinate-free Hilbert-space core first. This minimizes dependence on
pseudoinverses and makes the results more general than a particular matrix
representation.

## Cost and decision gates

| Deliverable | Rough effort | Decision value |
|---|---:|---|
| Pilot: projection, Moreau, cone operations, and double rejection | 4–8 person-weeks | High: exercises every central type and proof pattern. |
| Deterministic cone algebra in 4.1–4.6, including intersection and the error bound but excluding random JL | 4–8 person-months total | High if the core theory is the primary result. |
| Broad mathematical formalization of Sections 2–5 | 12–24 person-months | Medium; much of the effort is library work and specification repair. |
| Verification of biological validity | Not a Lean deliverable | Requires an empirical program and data. |

The ranges assume an experienced Lean developer, quick access to the author for
specification questions, and reuse of mathlib. For a new Lean user or an
upstream-quality requirement, cost may be at least twice as high.

### Pilot acceptance criteria

- exactly the quantification of (98): an arbitrary real Hilbert space and two closed
  convex cones;
- no `sorry`, custom axioms, or undeclared extra regularity assumptions;
- the paper's polar, closure, and operation conventions are documented and tested;
- Moreau and the point-to-cone transition are exposed through named reusable lemmas;
- at least one simple finite-dimensional regression example;
- actual code volume, library gaps, and elapsed effort drive a new estimate for (109),
  rather than this desk estimate.

### Stop or reformulate after the pilot if

- (98) can only be proved after strengthening or changing the claim in a way the
  author does not accept;
- most effort turns into general mathlib infrastructure with little value for the
  intended research result;
- the project's actual goal is biological evidence rather than conditional
  mathematical correctness.

## Conclusion

The paper is a credible Lean project if the goal is **formal verification of the cone
algebra and its conditional realization theorems**. The core is precise enough, the
proofs use standard Hilbert-space geometry, and a compiled probe demonstrates that
mathlib provides a viable foundation.

A complete line-by-line formalization would instead be a long-term library project,
and Lean verification would not by itself substantiate the CNS interpretation. The
rational next step is the bounded double-rejection pilot followed by a new go/no-go
gate.
