import IPNPCNS.Cone.MetricProjection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Structural laws for metric projection onto a cone

This file proves the two global projection properties used in equations (195) and
(196). Projection onto a closed cone is positively homogeneous. It also ignores the
component orthogonal to any orthogonally complemented subspace containing the cone;
in particular, it depends only on the component in the cone's real linear span when
that span is finite-dimensional.
-/

open Set

namespace IPNPCNS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Equation (196): projection onto a cone is homogeneous for nonnegative scalars. -/
theorem metricProjection_smul (C : ClosedCone H) (x : H) {a : ℝ} (ha : 0 ≤ a) :
    metricProjection C (a • x) = a • metricProjection C x := by
  rw [metricProjection_eq_iff]
  refine ⟨C.smul_mem (metricProjection_mem C x) ha, ?_, ?_⟩
  · rw [← smul_sub]
    exact (polar C).smul_mem (sub_metricProjection_mem_polar C x) ha
  · rw [← smul_sub, inner_smul_left, inner_smul_right,
      inner_metricProjection_sub_eq_zero, mul_zero, mul_zero]

/-- Projection onto a cone ignores the orthogonal complement of any orthogonally
complemented real subspace that contains the cone. -/
theorem metricProjection_starProjection_eq
    (C : ClosedCone H) (S : Submodule ℝ H) [S.HasOrthogonalProjection]
    (hCS : ∀ y ∈ C, y ∈ S) (x : H) :
    metricProjection C (S.starProjection x) = metricProjection C x := by
  apply metricProjection_eq_of_mem_of_inner_le_zero
  · exact metricProjection_mem C x
  · intro z hz
    have hpS : metricProjection C x ∈ S :=
      hCS _ (metricProjection_mem C x)
    have hzS : z ∈ S := hCS z hz
    have hdiffS : z - metricProjection C x ∈ S := S.sub_mem hzS hpS
    have horth : inner ℝ (x - S.starProjection x)
        (z - metricProjection C x) = 0 :=
      Submodule.starProjection_inner_eq_zero x _ hdiffS
    have hvar := metricProjection_inner_le_zero C x z hz
    have hsplit : x - metricProjection C x =
        (x - S.starProjection x) +
          (S.starProjection x - metricProjection C x) := by
      abel
    rw [hsplit, inner_add_left, horth, zero_add] at hvar
    exact hvar

/-- The real linear span of a closed cone. -/
def coneSpan (C : ClosedCone H) : Submodule ℝ H :=
  Submodule.span ℝ (C : Set H)

/-- Equation (195) under its exact analytic premise: if the cone span is
finite-dimensional, cone projection depends only on the orthogonal projection into
that span. The ambient Hilbert space may remain infinite-dimensional. -/
theorem metricProjection_coneSpan (C : ClosedCone H)
    [FiniteDimensional ℝ (coneSpan C)] (x : H) :
    metricProjection C x = metricProjection C ((coneSpan C).starProjection x) := by
  symm
  apply metricProjection_starProjection_eq C (coneSpan C)
  intro y hy
  exact Submodule.subset_span hy

end

end IPNPCNS
