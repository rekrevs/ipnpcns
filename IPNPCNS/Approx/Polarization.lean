import IPNPCNS.Approx.Invariance

/-!
# Polarization of a scaled near-isometry

This module derives equation (162) from equation (161) on a real linear subspace.
The balanced-vector polarization argument preserves the sharp distortion constant.
-/

namespace IPNPCNS

noncomputable section

variable {H H₂ : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]

/-- The bilinear error between the pulled-back inner product and its scaled target. -/
def scaledInnerError (M : H →L[ℝ] H₂) (α : ℝ) (u v : H) : ℝ :=
  inner ℝ (M u) (M v) - α * inner ℝ u v

/-- The diagonal consequence of the two-sided squared-norm estimate (161). -/
theorem abs_scaledInnerError_self_le
    {M : H →L[ℝ] H₂} {S : Set H} {α ρ : ℝ}
    (hM : ScaledNearIsometryOn M S α ρ)
    {u : H} (hu : u ∈ S) :
    |scaledInnerError M α u u| ≤ ρ * α * ‖u‖ ^ 2 := by
  have hlo := (hM u hu).1
  have hhi := (hM u hu).2
  rw [abs_le]
  constructor <;>
    simp only [scaledInnerError, real_inner_self_eq_norm_sq] <;>
    nlinarith

/-- Real polarization for the scaled inner-product error. -/
theorem scaledInnerError_add_sub
    (M : H →L[ℝ] H₂) (α : ℝ) (u v : H) :
    scaledInnerError M α (u + v) (u + v) -
        scaledInnerError M α (u - v) (u - v) =
      4 * scaledInnerError M α u v := by
  simp only [scaledInnerError, map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right]
  rw [real_inner_comm (M v) (M u), real_inner_comm v u]
  ring

/-- Equation (162): a scaled near-isometry on a real subspace controls all inner
products on that subspace with the same relative constant. -/
theorem scaledInnerDistortionOn_of_scaledNearIsometryOn_submodule
    {M : H →L[ℝ] H₂} (V : Submodule ℝ H) {α ρ : ℝ}
    (hM : ScaledNearIsometryOn M (V : Set H) α ρ)
    (hα : 0 < α) (hρ : 0 ≤ ρ) :
    ScaledInnerDistortionOn M (V : Set H) α ρ := by
  intro u hu v hv
  have hρα : 0 ≤ ρ * α := mul_nonneg hρ hα.le
  by_cases hu0 : u = 0
  · subst u
    simp
  by_cases hv0 : v = 0
  · subst v
    simp
  let a : ℝ := ‖v‖
  let b : ℝ := ‖u‖
  let up : H := a • u + b • v
  let um : H := a • u - b • v
  have ha : 0 < a := by
    simpa [a, norm_pos_iff] using hv0
  have hb : 0 < b := by
    simpa [b, norm_pos_iff] using hu0
  have hup : up ∈ V := V.add_mem (V.smul_mem a hu) (V.smul_mem b hv)
  have hum : um ∈ V := V.sub_mem (V.smul_mem a hu) (V.smul_mem b hv)
  have hp := abs_scaledInnerError_self_le hM hup
  have hm := abs_scaledInnerError_self_le hM hum
  have hpm :
      |scaledInnerError M α up up - scaledInnerError M α um um| ≤
        ρ * α * (‖up‖ ^ 2 + ‖um‖ ^ 2) := by
    rw [abs_le] at hp hm ⊢
    constructor <;> nlinarith [hρα]
  have hpolar :
      scaledInnerError M α up up - scaledInnerError M α um um =
        4 * a * b * scaledInnerError M α u v := by
    calc
      scaledInnerError M α up up - scaledInnerError M α um um =
          4 * scaledInnerError M α (a • u) (b • v) := by
        simpa [up, um] using scaledInnerError_add_sub M α (a • u) (b • v)
      _ = 4 * a * b * scaledInnerError M α u v := by
        simp only [scaledInnerError, map_smul, inner_smul_left, inner_smul_right,
          conj_trivial]
        ring
  have hnorm : ‖up‖ ^ 2 + ‖um‖ ^ 2 = 4 * a ^ 2 * b ^ 2 := by
    calc
      ‖up‖ ^ 2 + ‖um‖ ^ 2 =
          2 * (‖a • u‖ ^ 2 + ‖b • v‖ ^ 2) := by
        simpa [up, um] using parallelogram_law_with_norm ℝ (a • u) (b • v)
      _ = 4 * a ^ 2 * b ^ 2 := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb]
        dsimp [a, b]
        ring
  have hscaled :
      (4 * a * b) * |scaledInnerError M α u v| ≤
        (4 * a * b) * (ρ * α * a * b) := by
    rw [hpolar, hnorm] at hpm
    calc
      (4 * a * b) * |scaledInnerError M α u v| =
          |4 * a * b * scaledInnerError M α u v| := by
        rw [abs_mul]
        congr 1
        exact (abs_of_pos (by positivity : 0 < 4 * a * b)).symm
      _ ≤ ρ * α * (4 * a ^ 2 * b ^ 2) := hpm
      _ = (4 * a * b) * (ρ * α * a * b) := by ring
  have herr :
      |scaledInnerError M α u v| ≤ ρ * α * a * b :=
    le_of_mul_le_mul_left hscaled (by positivity : 0 < 4 * a * b)
  change |scaledInnerError M α u v| ≤ ρ * α * ‖u‖ * ‖v‖
  convert herr using 1
  dsimp [a, b]
  ring

end

end IPNPCNS
