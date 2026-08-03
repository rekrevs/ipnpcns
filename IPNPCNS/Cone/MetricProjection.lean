import IPNPCNS.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Metric projection onto a closed convex cone

The projection is noncomputable: it selects the unique closest point whose existence is
provided by the Hilbert projection theorem.
-/

open Set

namespace IPNPCNS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem exists_metricProjection (C : ClosedCone H) (x : H) :
    ∃ y ∈ C, ‖x - y‖ = ⨅ z : C, ‖x - z‖ :=
  exists_norm_eq_iInf_of_complete_convex C.nonempty C.isClosed.isComplete C.convex x

/-- Equation (65): metric projection onto a closed convex cone. -/
def metricProjection (C : ClosedCone H) (x : H) : H :=
  Classical.choose (exists_metricProjection C x)

theorem metricProjection_mem (C : ClosedCone H) (x : H) :
    metricProjection C x ∈ C :=
  (Classical.choose_spec (exists_metricProjection C x)).1

theorem metricProjection_minimal (C : ClosedCone H) (x : H) :
    ‖x - metricProjection C x‖ = ⨅ z : C, ‖x - z‖ :=
  (Classical.choose_spec (exists_metricProjection C x)).2

/-- Equation (69): the variational characterization of the chosen projection. -/
theorem metricProjection_inner_le_zero (C : ClosedCone H) (x : H) :
    ∀ y ∈ C, inner ℝ (x - metricProjection C x) (y - metricProjection C x) ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero C.convex (metricProjection_mem C x)).mp
    (metricProjection_minimal C x)

/-- A point satisfying the variational condition is the chosen metric projection. -/
theorem metricProjection_eq_of_mem_of_inner_le_zero (C : ClosedCone H) (x y : H)
    (hy : y ∈ C)
    (hvar : ∀ z ∈ C, inner ℝ (x - y) (z - y) ≤ 0) :
    metricProjection C x = y := by
  let p := metricProjection C x
  have hp : p ∈ C := metricProjection_mem C x
  have hp_to_y : inner ℝ (x - p) (y - p) ≤ 0 :=
    metricProjection_inner_le_zero C x y hy
  have hy_to_p : inner ℝ (x - y) (p - y) ≤ 0 := hvar p hp
  have hnonneg : 0 ≤ inner ℝ (x - p) (p - y) := by
    rw [show p - y = -(y - p) by abel, inner_neg_right]
    linarith
  have hsplit : x - y = (x - p) + (p - y) := by abel
  rw [hsplit, inner_add_left, real_inner_self_eq_norm_sq] at hy_to_p
  have hnorm : ‖p - y‖ = 0 := by
    nlinarith [sq_nonneg ‖p - y‖]
  have : p = y := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  exact this

/-- The residual from projection lies in the paper's polar cone. -/
theorem sub_metricProjection_mem_polar (C : ClosedCone H) (x : H) :
    x - metricProjection C x ∈ polar C := by
  rw [mem_polar]
  intro y hy
  let p := metricProjection C x
  have hp : p ∈ C := metricProjection_mem C x
  have h := metricProjection_inner_le_zero C x (y + p) (C.add_mem hy hp)
  simpa [p] using h

/-- The projection and its residual are orthogonal. -/
theorem inner_metricProjection_sub_eq_zero (C : ClosedCone H) (x : H) :
    inner ℝ (metricProjection C x) (x - metricProjection C x) = 0 := by
  let p := metricProjection C x
  have hp : p ∈ C := metricProjection_mem C x
  have hzero := metricProjection_inner_le_zero C x 0 C.zero_mem
  have htwo := metricProjection_inner_le_zero C x (2 • p)
    (C.smul_mem hp (by norm_num : (0 : ℝ) ≤ 2))
  have hge : 0 ≤ inner ℝ (x - p) p := by
    simpa [p] using hzero
  have hle : inner ℝ (x - p) p ≤ 0 := by
    simpa [p, two_smul ℝ p] using htwo
  have h : inner ℝ (x - p) p = 0 := le_antisymm hle hge
  simpa [p, real_inner_comm] using h

/-- Equation (70), converse direction: an orthogonal cone–polar decomposition
identifies the metric projection. -/
theorem metricProjection_eq_of_mem_of_mem_polar_inner_eq_zero
    (C : ClosedCone H) (x y z : H) (hy : y ∈ C) (hz : z ∈ polar C)
    (horth : inner ℝ y z = 0) (hsum : x = y + z) :
    metricProjection C x = y := by
  apply metricProjection_eq_of_mem_of_inner_le_zero C x y hy
  intro w hw
  rw [hsum]
  have hzw : inner ℝ z w ≤ 0 := (mem_polar.mp hz) w hw
  have hzy : inner ℝ z y = 0 := by simpa [real_inner_comm] using horth
  rw [show y + z - y = z by abel, inner_sub_right, hzy, sub_zero]
  exact hzw

/-- Equation (70): membership in the cone, polar residual, and orthogonality
characterize the chosen metric projection. -/
theorem metricProjection_eq_iff (C : ClosedCone H) (x y : H) :
    metricProjection C x = y ↔
      y ∈ C ∧ x - y ∈ polar C ∧ inner ℝ y (x - y) = 0 := by
  constructor
  · intro h
    subst y
    exact ⟨metricProjection_mem C x, sub_metricProjection_mem_polar C x,
      inner_metricProjection_sub_eq_zero C x⟩
  · rintro ⟨hy, hz, horth⟩
    exact metricProjection_eq_of_mem_of_mem_polar_inner_eq_zero C x y (x - y)
      hy hz horth (by abel)

end

end IPNPCNS
