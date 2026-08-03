import IPNPCNS.Cone.MetricProjection

/-!
# Moreau decomposition for closed convex cones

This module proves equations (67)–(71) in the paper's non-positive-polar
convention.
-/

namespace IPNPCNS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Equation (71): projection onto the polar is the residual from projection onto the
original cone. -/
theorem metricProjection_polar_eq_sub (C : ClosedCone H) (x : H) :
    metricProjection (polar C) x = x - metricProjection C x := by
  apply metricProjection_eq_of_mem_of_mem_polar_inner_eq_zero
    (polar C) x (x - metricProjection C x) (metricProjection C x)
  · exact sub_metricProjection_mem_polar C x
  · exact subset_polar_polar C (metricProjection_mem C x)
  · simpa [real_inner_comm] using inner_metricProjection_sub_eq_zero C x
  · abel

/-- The additive identity in Moreau decomposition, equation (67). -/
theorem moreau_add (C : ClosedCone H) (x : H) :
    x = metricProjection C x + metricProjection (polar C) x := by
  rw [metricProjection_polar_eq_sub]
  abel

/-- The orthogonality identity in Moreau decomposition, equation (67). -/
theorem moreau_inner (C : ClosedCone H) (x : H) :
    inner ℝ (metricProjection C x) (metricProjection (polar C) x) = 0 := by
  rw [metricProjection_polar_eq_sub]
  exact inner_metricProjection_sub_eq_zero C x

/-- Equation (68): any cone–polar orthogonal decomposition is the Moreau
decomposition. -/
theorem moreau_unique (C : ClosedCone H) (x y z : H)
    (hy : y ∈ C) (hz : z ∈ polar C) (horth : inner ℝ y z = 0)
    (hsum : x = y + z) :
    metricProjection C x = y ∧ metricProjection (polar C) x = z := by
  have hyproj :=
    metricProjection_eq_of_mem_of_mem_polar_inner_eq_zero C x y z hy hz horth hsum
  constructor
  · exact hyproj
  · rw [metricProjection_polar_eq_sub, hyproj]
    rw [hsum]
    abel

/-- Equation (95): the polar of the polar of a closed convex cone is the original
cone. -/
theorem polar_polar (C : ClosedCone H) : polar (polar C) = C := by
  apply le_antisymm
  · intro x hx
    have hresidual :=
      (mem_polar.mp hx) (x - metricProjection C x)
        (sub_metricProjection_mem_polar C x)
    have hinner :
        inner ℝ x (x - metricProjection C x) =
          inner ℝ (metricProjection C x) (x - metricProjection C x) +
            inner ℝ (x - metricProjection C x) (x - metricProjection C x) := by
      rw [← inner_add_left]
      congr 1
      abel
    rw [hinner, inner_metricProjection_sub_eq_zero, zero_add,
      real_inner_self_eq_norm_sq] at hresidual
    have hnorm : ‖x - metricProjection C x‖ = 0 := by
      nlinarith [sq_nonneg ‖x - metricProjection C x‖]
    have hxproj : x = metricProjection C x :=
      sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    rw [hxproj]
    exact metricProjection_mem C x
  · exact subset_polar_polar C

end

end IPNPCNS
