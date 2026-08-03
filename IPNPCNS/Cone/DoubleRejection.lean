import IPNPCNS.Cone.Operations

/-!
# Conic projection by double rejection

This module proves equations (98) and (108), the first new headline identity in the
paper.
-/

namespace IPNPCNS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Equation (103): for `x ∈ A`, projection onto `B` equals projection onto the
polar of `A` rejected by `B`. -/
theorem metricProjection_polar_rejection_eq (A B : ClosedCone H) (x : H)
    (hx : x ∈ A) :
    metricProjection (polar (coneRejection A B)) x = metricProjection B x := by
  apply metricProjection_eq_of_mem_of_mem_polar_inner_eq_zero
    (polar (coneRejection A B)) x
    (metricProjection B x) (metricProjection (polar B) x)
  · exact polar_antitone (coneRejection_le_polar A B)
      (subset_polar_polar B (metricProjection_mem B x))
  · exact subset_polar_polar (coneRejection A B)
      (metricProjection_polar_mem_coneRejection A B hx)
  · exact moreau_inner B x
  · exact moreau_add B x

/-- Equations (98)/(108): conic projection is two successive conic rejections. -/
theorem doubleRejection (A B : ClosedCone H) :
    coneProjection A B = coneRejection A (coneRejection A B) := by
  change coneProjection A B =
    coneProjection A (polar (coneRejection A B))
  apply le_antisymm
  · change conicHull (projectedSet A B) ≤
      coneProjection A (polar (coneRejection A B))
    apply conicHull_le
    rintro y ⟨x, hx, rfl⟩
    have hgen :=
      metricProjection_mem_coneProjection A (polar (coneRejection A B)) hx
    rw [metricProjection_polar_rejection_eq A B x hx] at hgen
    exact hgen
  · change conicHull (projectedSet A (polar (coneRejection A B))) ≤
      coneProjection A B
    apply conicHull_le
    rintro y ⟨x, hx, rfl⟩
    rw [metricProjection_polar_rejection_eq A B x hx]
    exact metricProjection_mem_coneProjection A B hx

end

end IPNPCNS
