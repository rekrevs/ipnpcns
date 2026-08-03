import IPNPCNS.Cone.Intersection

/-!
# Deterministic approximate invariance

This module separates the deterministic assumptions in equations (161) and (162) from
their consequences and verifies the projection-error calculation (165)–(167).
-/

namespace IPNPCNS

noncomputable section

variable {H H₂ : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]

/-- Equation (161), expressed on an explicit set of relevant vectors. -/
def ScaledNearIsometryOn (M : H →L[ℝ] H₂) (S : Set H) (α ρ : ℝ) : Prop :=
  ∀ u ∈ S,
    (1 - ρ) * α * ‖u‖ ^ 2 ≤ ‖M u‖ ^ 2 ∧
      ‖M u‖ ^ 2 ≤ (1 + ρ) * α * ‖u‖ ^ 2

/-- Equation (162), kept as an explicit deterministic interface. -/
def ScaledInnerDistortionOn (M : H →L[ℝ] H₂) (S : Set H) (α ρ : ℝ) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S,
    |inner ℝ (M u) (M v) - α * inner ℝ u v| ≤
      ρ * α * ‖u‖ * ‖v‖

/-- Equation (163), positive-sign direction. -/
theorem inner_map_pos_of_margin
    {M : H →L[ℝ] H₂} {S : Set H} {α ρ : ℝ}
    (hα : 0 < α)
    (hM : ScaledInnerDistortionOn M S α ρ)
    {u v : H} (hu : u ∈ S) (hv : v ∈ S)
    (hmargin : ρ * ‖u‖ * ‖v‖ < inner ℝ u v) :
    0 < inner ℝ (M u) (M v) := by
  have hdist := (abs_le.mp (hM u hu v hv)).1
  have hnorms : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- Equation (163), negative-sign direction. -/
theorem inner_map_neg_of_margin
    {M : H →L[ℝ] H₂} {S : Set H} {α ρ : ℝ}
    (hα : 0 < α)
    (hM : ScaledInnerDistortionOn M S α ρ)
    {u v : H} (hu : u ∈ S) (hv : v ∈ S)
    (hmargin : inner ℝ u v < -(ρ * ‖u‖ * ‖v‖)) :
    inner ℝ (M u) (M v) < 0 := by
  have hdist := (abs_le.mp (hM u hu v hv)).2
  have hnorms : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

variable [CompleteSpace H]

/-- Equation (166): metric-projection optimality gives a Pythagorean lower bound. -/
theorem projection_pythagorean_lower
    (B : ClosedCone H) (x q : H) (hq : q ∈ B) :
    ‖x - metricProjection B x‖ ^ 2 +
        ‖q - metricProjection B x‖ ^ 2 ≤
      ‖x - q‖ ^ 2 := by
  have hvar :=
    metricProjection_inner_le_zero B x q hq
  have hdecomp :
      x - q = (x - metricProjection B x) - (q - metricProjection B x) := by
    abel
  calc
    ‖x - metricProjection B x‖ ^ 2 +
          ‖q - metricProjection B x‖ ^ 2 ≤
        ‖x - metricProjection B x‖ ^ 2 -
            2 * inner ℝ (x - metricProjection B x)
              (q - metricProjection B x) +
          ‖q - metricProjection B x‖ ^ 2 := by
      nlinarith
    _ = ‖(x - metricProjection B x) -
          (q - metricProjection B x)‖ ^ 2 := by
      exact (norm_sub_sq_real (x - metricProjection B x)
        (q - metricProjection B x)).symm
    _ = ‖x - q‖ ^ 2 := by rw [hdecomp]

omit [CompleteSpace H] in
/-- Equation (165), derived from lower/upper scaled near-isometry bounds and
transformed-space optimality. -/
theorem distance_ratio_of_scaled_bounds
    {M : H →L[ℝ] H₂} {α ρ : ℝ} (hα : 0 < α) (hρ : ρ < 1)
    (x p q : H)
    (hlower :
      (1 - ρ) * α * ‖x - q‖ ^ 2 ≤ ‖M (x - q)‖ ^ 2)
    (hupper :
      ‖M (x - p)‖ ^ 2 ≤ (1 + ρ) * α * ‖x - p‖ ^ 2)
    (hoptimal : ‖M (x - q)‖ ≤ ‖M (x - p)‖) :
    ‖x - q‖ ^ 2 ≤ ((1 + ρ) / (1 - ρ)) * ‖x - p‖ ^ 2 := by
  have hoptSq :
      ‖M (x - q)‖ ^ 2 ≤ ‖M (x - p)‖ ^ 2 := by
    simpa [pow_two] using
      mul_self_le_mul_self (norm_nonneg (M (x - q))) hoptimal
  have hchain :
      (1 - ρ) * α * ‖x - q‖ ^ 2 ≤
        (1 + ρ) * α * ‖x - p‖ ^ 2 :=
    hlower.trans (hoptSq.trans hupper)
  have hchain' :
      α * ((1 - ρ) * ‖x - q‖ ^ 2) ≤
        α * ((1 + ρ) * ‖x - p‖ ^ 2) := by
    convert hchain using 1 <;> ring
  have hscaled :
      (1 - ρ) * ‖x - q‖ ^ 2 ≤
        (1 + ρ) * ‖x - p‖ ^ 2 :=
    le_of_mul_le_mul_left hchain' hα
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  simpa [mul_comm] using hscaled

omit [CompleteSpace H] in
/-- Equation (165), using equation (161) on the two required residual vectors. -/
theorem distance_ratio_of_scaledNearIsometryOn
    {M : H →L[ℝ] H₂} {S : Set H} {α ρ : ℝ}
    (hM : ScaledNearIsometryOn M S α ρ)
    (hα : 0 < α) (hρ : ρ < 1)
    (x p q : H) (hxq : x - q ∈ S) (hxp : x - p ∈ S)
    (hoptimal : ‖M (x - q)‖ ≤ ‖M (x - p)‖) :
    ‖x - q‖ ^ 2 ≤ ((1 + ρ) / (1 - ρ)) * ‖x - p‖ ^ 2 :=
  distance_ratio_of_scaled_bounds hα hρ x p q
    (hM (x - q) hxq).1 (hM (x - p) hxp).2 hoptimal

/-- The squared form of equation (167). -/
theorem projection_error_sq
    (B : ClosedCone H) (x q : H) (hq : q ∈ B)
    {ρ : ℝ} (hρ : ρ < 1)
    (hratio :
      ‖x - q‖ ^ 2 ≤ ((1 + ρ) / (1 - ρ)) *
        ‖x - metricProjection B x‖ ^ 2) :
    ‖q - metricProjection B x‖ ^ 2 ≤
      (2 * ρ / (1 - ρ)) * ‖x - metricProjection B x‖ ^ 2 := by
  have hpyth := projection_pythagorean_lower B x q hq
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ
  have hratioDiv :
      ‖x - q‖ ^ 2 ≤
        ((1 + ρ) * ‖x - metricProjection B x‖ ^ 2) / (1 - ρ) := by
    simpa only [div_mul_eq_mul_div] using hratio
  have hratio' :
      ‖x - q‖ ^ 2 * (1 - ρ) ≤
        (1 + ρ) * ‖x - metricProjection B x‖ ^ 2 := by
    exact (le_div_iff₀ hden).mp hratioDiv
  have hpyth' := mul_le_mul_of_nonneg_right hpyth (le_of_lt hden)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  nlinarith only [hpyth', hratio']

/-- Equation (167), in the paper's norm form. -/
theorem projection_error
    (B : ClosedCone H) (x q : H) (hq : q ∈ B)
    {ρ : ℝ} (hρnonneg : 0 ≤ ρ) (hρ : ρ < 1)
    (hratio :
      ‖x - q‖ ^ 2 ≤ ((1 + ρ) / (1 - ρ)) *
        ‖x - metricProjection B x‖ ^ 2) :
    ‖q - metricProjection B x‖ ≤
      √(2 * ρ / (1 - ρ)) * ‖x - metricProjection B x‖ := by
  have hsq := projection_error_sq B x q hq hρ hratio
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ
  have hcoef : 0 ≤ 2 * ρ / (1 - ρ) :=
    div_nonneg (mul_nonneg (by norm_num) hρnonneg) (le_of_lt hden)
  apply nonneg_le_nonneg_of_sq_le_sq
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hsqrt := Real.sq_sqrt hcoef
  nlinarith

/-- Equations (165)–(167), with the relevant-vector coverage made explicit. -/
theorem projection_error_of_scaledNearIsometryOn
    {M : H →L[ℝ] H₂} {S : Set H} {α ρ : ℝ}
    (hM : ScaledNearIsometryOn M S α ρ)
    (hα : 0 < α) (hρnonneg : 0 ≤ ρ) (hρ : ρ < 1)
    (B : ClosedCone H) (x q : H) (hq : q ∈ B)
    (hxq : x - q ∈ S)
    (hxp : x - metricProjection B x ∈ S)
    (hoptimal :
      ‖M (x - q)‖ ≤ ‖M (x - metricProjection B x)‖) :
    ‖q - metricProjection B x‖ ≤
      √(2 * ρ / (1 - ρ)) * ‖x - metricProjection B x‖ := by
  apply projection_error B x q hq hρnonneg hρ
  exact distance_ratio_of_scaledNearIsometryOn hM hα hρ x
    (metricProjection B x) q hxq hxp hoptimal

end

end IPNPCNS
