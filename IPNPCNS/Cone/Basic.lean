import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Closed convex cones in the paper's conventions

This module fixes the representation and sign conventions used by the cone algebra in
Section 4 of the paper.
-/

open Set
open scoped Pointwise

namespace IPNPCNS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A closed convex cone in the sense used in Section 4. -/
abbrev ClosedCone (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :=
  ProperCone ℝ H

/-- Equation (62): the norm-closed conic hull of a set. -/
def conicHull (s : Set H) : ClosedCone H where
  toSubmodule := (PointedCone.hull ℝ s).closure
  isClosed' := isClosed_closure

theorem subset_conicHull (s : Set H) : s ⊆ conicHull s := by
  intro x hx
  exact subset_closure (PointedCone.subset_hull hx)

theorem conicHull_le {s : Set H} {C : ClosedCone H} (hs : s ⊆ C) :
    conicHull s ≤ C := by
  intro x hx
  exact C.isClosed.closure_subset_iff.2 (Submodule.span_le.2 hs) hx

theorem conicHull_mono {s t : Set H} (hst : s ⊆ t) :
    conicHull s ≤ conicHull t :=
  conicHull_le (hst.trans (subset_conicHull t))

variable [CompleteSpace H]

/-- Equation (66): the paper's non-positive polar cone.

Mathlib's dual cone uses a nonnegative pairing, so this is the dual of the reflected
carrier.
-/
def polar (C : ClosedCone H) : ClosedCone H :=
  ProperCone.dual (innerₗ H) (-(C : Set H))

theorem mem_polar {C : ClosedCone H} {z : H} :
    z ∈ polar C ↔ ∀ y ∈ C, inner ℝ z y ≤ 0 := by
  constructor
  · intro hz y hy
    have hneg : -y ∈ -(C : Set H) := by
      change -(-y) ∈ C
      simpa using hy
    have h := (ProperCone.mem_dual.mp hz) hneg
    simpa [real_inner_comm] using h
  · intro hz
    apply ProperCone.mem_dual.mpr
    intro x hx
    change -x ∈ C at hx
    simpa [real_inner_comm] using hz (-x) hx

theorem polar_antitone {C D : ClosedCone H} (h : C ≤ D) : polar D ≤ polar C := by
  intro z hz
  rw [mem_polar] at hz ⊢
  exact fun y hy => hz y (h hy)

theorem subset_polar_polar (C : ClosedCone H) : C ≤ polar (polar C) := by
  intro x hx
  rw [mem_polar]
  intro z hz
  rw [mem_polar] at hz
  simpa [real_inner_comm] using hz x hx

end

end IPNPCNS
