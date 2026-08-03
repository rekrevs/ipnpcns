import IPNPCNS.Cone.Moreau

/-!
# Cone operations

This module formalizes the closure-safe conic projection and rejection operations from
equations (73) and (74).
-/

open Set

namespace IPNPCNS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The pointwise projections used as generators in equation (73). -/
def projectedSet (A B : ClosedCone H) : Set H :=
  metricProjection B '' (A : Set H)

/-- Equation (73): the closed conic hull of all pointwise projections from `A` onto
`B`. -/
def coneProjection (A B : ClosedCone H) : ClosedCone H :=
  conicHull (projectedSet A B)

/-- Equation (74): conic rejection is conic projection onto the polar. -/
def coneRejection (A B : ClosedCone H) : ClosedCone H :=
  coneProjection A (polar B)

theorem metricProjection_mem_coneProjection (A B : ClosedCone H) {x : H}
    (hx : x ∈ A) : metricProjection B x ∈ coneProjection A B :=
  subset_conicHull (projectedSet A B) ⟨x, hx, rfl⟩

theorem coneProjection_le_right (A B : ClosedCone H) : coneProjection A B ≤ B := by
  apply conicHull_le
  rintro y ⟨x, _hx, rfl⟩
  exact metricProjection_mem B x

theorem metricProjection_polar_mem_coneRejection (A B : ClosedCone H) {x : H}
    (hx : x ∈ A) : metricProjection (polar B) x ∈ coneRejection A B :=
  metricProjection_mem_coneProjection A (polar B) hx

theorem coneRejection_le_polar (A B : ClosedCone H) : coneRejection A B ≤ polar B :=
  coneProjection_le_right A (polar B)

/-- The residual-generator form of equation (74). -/
theorem coneRejection_eq_residualHull (A B : ClosedCone H) :
    coneRejection A B =
      conicHull ((fun x => x - metricProjection B x) '' (A : Set H)) := by
  unfold coneRejection coneProjection projectedSet
  congr 1
  ext y
  simp only [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (metricProjection_polar_eq_sub B x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, metricProjection_polar_eq_sub B x⟩

end

end IPNPCNS
