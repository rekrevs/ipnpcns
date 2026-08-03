# Formalization Specification

## Scope

The first formalization layer targets the coordinate-free cone algebra in Sections
4.1–4.5 of `2309.02332v3.pdf`. Its principal acceptance theorem is the double
rejection identity (98)/(108) for arbitrary closed convex cones in a real Hilbert
space.

The following layers are intentionally separate:

- finitely generated and polyhedral cones used by the neural representation;
- finite-dimensional matrices, singular values, and Moore–Penrose pseudoinverses;
- deterministic approximate invariance;
- NNLS and stochastic learning;
- conditional population realization and empirical interpretation.

## Ambient space

`H` is an arbitrary real Hilbert space:

```lean
[NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
```

The cone core must not assume finite dimension or finite generation.

## Paper-to-Lean conventions

| Paper object | Lean interpretation |
|---|---|
| closed convex cone | `ClosedCone H`, an alias of `ProperCone ℝ H` |
| `Conic(s)`, (62) | norm closure of `PointedCone.hull ℝ s` |
| `P_a x`, (65) | a noncomputable chosen metric minimizer, proved unique extensionally |
| `¬a`, (66) | vectors `z` satisfying `inner ℝ z y ≤ 0` for all `y ∈ a` |
| `a + b`, (72) | closed conic hull of the pointwise Minkowski sum |
| `a ⌞ b`, (73) | closed conic hull of pointwise metric projections of points of `a` onto `b` |
| `a ¬ b`, (74) | `a ⌞ polar b`; Moreau later proves the residual-generator form |
| equality of cones | extensional equality of their carriers |

Mathlib's dual cone uses a nonnegative pairing. The paper's polar uses a nonpositive
inner product, so the implementation defines it through the dual of the reflected
carrier and exposes a paper-facing membership theorem. All later proofs use that
membership theorem rather than relying on the implementation sign convention.

Every hull and cone image in the Section 4.5 layer is norm-topologically closed.
Pointwise images are never silently identified with their closed conic hulls.

## T-0003 target

The headline theorem must have the following mathematical content:

```text
For every real Hilbert space H and closed convex cones a and b in H,
  coneProjection a b = coneRejection a (coneRejection a b).
```

The proof must include:

1. metric-projection membership, minimality, uniqueness, and the variational
   characterization corresponding to (65), (68), and (69);
2. the cone-specific residual/polar/orthogonality characterization (70);
3. Moreau decomposition and the residual identity (67)–(71);
4. closure-safe definitions of conic projection and rejection;
5. the pointwise equality used in (103), followed by a separate lift to equality of
   closed conic hulls.

## Non-goals of the first gate

- computability or code extraction for metric projection;
- a Moore–Penrose pseudoinverse implementation;
- finite-frame algorithms;
- stochastic convergence;
- empirical validation of the CNS interpretation;
- upstreaming the new general-purpose lemmas to mathlib.

No theorem may use `sorry`, a custom axiom, or an assumption stronger than this
specification without recording a project-control checkpoint.
