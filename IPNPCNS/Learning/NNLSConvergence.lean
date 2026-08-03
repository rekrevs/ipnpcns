import IPNPCNS.Learning.NNLSOptimality

/-!
# Deterministic projected-batch convergence

This module proves geometric convergence of the projected batch update under an
explicit spectral contraction hypothesis for `I - ε X Xᵀ`. It does not infer a
stochastic result from the paper's unspecified “standard assumptions”.
-/

open scoped BigOperators

namespace IPNPCNS

noncomputable section

variable {n N : ℕ}

/-- Squared Euclidean energy of a finite coefficient vector. -/
def coefficientEnergy (u : Fin n → ℝ) : ℝ :=
  ∑ i, u i ^ 2

theorem coefficientEnergy_nonneg (u : Fin n → ℝ) :
    0 ≤ coefficientEnergy u :=
  Finset.sum_nonneg fun i _ => sq_nonneg (u i)

/-- Componentwise projection onto the nonnegative orthant is nonexpansive in squared
Euclidean energy. -/
theorem coefficientEnergy_positivePart_sub_le (u v : Fin n → ℝ) :
    coefficientEnergy (positivePart u - positivePart v) ≤
      coefficientEnergy (u - v) := by
  unfold coefficientEnergy
  apply Finset.sum_le_sum
  intro i hi
  have habs : |positivePart u i - positivePart v i| ≤ |u i - v i| := by
    simpa only [positivePart, max_comm] using
      abs_max_sub_max_le_abs (u i) (v i) 0
  have hs := mul_self_le_mul_self (abs_nonneg _) habs
  simpa only [Pi.sub_apply, ← pow_two, sq_abs] using hs

theorem nnlsPrediction_sub
    (X : Matrix (Fin n) (Fin N) ℝ) (w v : Fin n → ℝ) :
    nnlsPrediction X (w - v) = nnlsPrediction X w - nnlsPrediction X v := by
  funext j
  simp only [nnlsPrediction, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
    Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem nnlsGradient_sub
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (w v : Fin n → ℝ) :
    nnlsGradient X y w - nnlsGradient X y v =
      X.mulVec (nnlsPrediction X (w - v)) := by
  funext i
  simp only [nnlsGradient, Matrix.mulVec, dotProduct, Pi.sub_apply]
  rw [nnlsPrediction_sub]
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The linear error step `(I - ε X Xᵀ)h` underlying the affine batch update. -/
def batchLinearErrorStep
    (X : Matrix (Fin n) (Fin N) ℝ) (ε : ℝ)
    (h : Fin n → ℝ) : Fin n → ℝ :=
  h - ε • X.mulVec (nnlsPrediction X h)

/-- One deterministic projected batch-gradient step. -/
def projectedBatchStep
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε : ℝ) (w : Fin n → ℝ) : Fin n → ℝ :=
  projectedUpdate ε (nnlsGradient X y w) w

theorem projectedBatchStep_eq_positivePart
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε : ℝ) (w : Fin n → ℝ) :
    projectedBatchStep X y ε w =
      positivePart (w - ε • nnlsGradient X y w) := by
  rfl

theorem projectedBatchStep_nonnegative
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε : ℝ) (w : Fin n → ℝ) :
    IsNonnegative (projectedBatchStep X y ε w) := by
  intro i
  exact le_max_left 0 (w i - ε * nnlsGradient X y w i)

/-- For a positive step, fixed points of the deterministic batch step are exactly the
global NNLS minimizers. -/
theorem projectedBatchStep_fixed_iff_nnlsMinimizer
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    {ε : ℝ} (hε : 0 < ε) (w : Fin n → ℝ) :
    projectedBatchStep X y ε w = w ↔ IsNNLSMinimizer X y w := by
  rw [projectedBatchStep, projectedBatchUpdate_fixed_iff_kkt hε,
    nnlsMinimizer_iff_complementaryKKT]

theorem rawBatchStep_sub
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε : ℝ) (w v : Fin n → ℝ) :
    (w - ε • nnlsGradient X y w) -
        (v - ε • nnlsGradient X y v) =
      batchLinearErrorStep X ε (w - v) := by
  rw [batchLinearErrorStep]
  rw [← nnlsGradient_sub X y w v]
  module

/-- Explicit spectral condition
`‖(I - ε X Xᵀ)h‖₂² ≤ q² ‖h‖₂²` for every coefficient error `h`. -/
def BatchLinearContraction
    (X : Matrix (Fin n) (Fin N) ℝ) (ε q : ℝ) : Prop :=
  ∀ h, coefficientEnergy (batchLinearErrorStep X ε h) ≤
    q ^ 2 * coefficientEnergy h

/-- The projected batch step inherits the unprojected spectral contraction because
orthant projection is nonexpansive. -/
theorem projectedBatchStep_energy_sub_le
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε q : ℝ) (hcontract : BatchLinearContraction X ε q)
    (w v : Fin n → ℝ) :
    coefficientEnergy
        (projectedBatchStep X y ε w - projectedBatchStep X y ε v) ≤
      q ^ 2 * coefficientEnergy (w - v) := by
  rw [projectedBatchStep_eq_positivePart, projectedBatchStep_eq_positivePart]
  calc
    coefficientEnergy
        (positivePart (w - ε • nnlsGradient X y w) -
          positivePart (v - ε • nnlsGradient X y v)) ≤
      coefficientEnergy
        ((w - ε • nnlsGradient X y w) -
          (v - ε • nnlsGradient X y v)) :=
      coefficientEnergy_positivePart_sub_le _ _
    _ = coefficientEnergy (batchLinearErrorStep X ε (w - v)) := by
      rw [rawBatchStep_sub]
    _ ≤ q ^ 2 * coefficientEnergy (w - v) := hcontract (w - v)

/-- Repeated deterministic projected batch updates. -/
def projectedBatchIterate
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ) (ε : ℝ)
    (w₀ : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => w₀
  | k + 1 => projectedBatchStep X y ε (projectedBatchIterate X y ε w₀ k)

/-- Geometric squared-error estimate toward any fixed point. -/
theorem projectedBatchIterate_energy_le
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε q : ℝ) (hcontract : BatchLinearContraction X ε q)
    (wstar w₀ : Fin n → ℝ)
    (hfixed : projectedBatchStep X y ε wstar = wstar) :
    ∀ k, coefficientEnergy (projectedBatchIterate X y ε w₀ k - wstar) ≤
      (q ^ 2) ^ k * coefficientEnergy (w₀ - wstar) := by
  intro k
  induction k with
  | zero => simp [projectedBatchIterate]
  | succ k ih =>
      rw [projectedBatchIterate]
      calc
        coefficientEnergy
            (projectedBatchStep X y ε (projectedBatchIterate X y ε w₀ k) -
              wstar) =
          coefficientEnergy
            (projectedBatchStep X y ε (projectedBatchIterate X y ε w₀ k) -
              projectedBatchStep X y ε wstar) := by rw [hfixed]
        _ ≤ q ^ 2 *
            coefficientEnergy (projectedBatchIterate X y ε w₀ k - wstar) :=
          projectedBatchStep_energy_sub_le X y ε q hcontract _ _
        _ ≤ q ^ 2 *
            ((q ^ 2) ^ k * coefficientEnergy (w₀ - wstar)) := by
          exact mul_le_mul_of_nonneg_left ih (sq_nonneg q)
        _ = (q ^ 2) ^ (k + 1) * coefficientEnergy (w₀ - wstar) := by
          rw [pow_succ]
          ring

/-- Under `0 ≤ q < 1`, the squared coefficient error converges to zero. -/
theorem projectedBatchIterate_energy_tendsto_zero
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε q : ℝ) (hcontract : BatchLinearContraction X ε q)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (wstar w₀ : Fin n → ℝ)
    (hfixed : projectedBatchStep X y ε wstar = wstar) :
    Filter.Tendsto (fun k =>
      coefficientEnergy (projectedBatchIterate X y ε w₀ k - wstar))
      Filter.atTop (nhds 0) := by
  have hq2 : q ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hq1) (by linarith : 0 < 1 + q)]
  have hbound : Filter.Tendsto
      (fun k => (q ^ 2) ^ k * coefficientEnergy (w₀ - wstar))
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg q) hq2).mul_const
        (coefficientEnergy (w₀ - wstar))
  exact squeeze_zero
    (fun k => coefficientEnergy_nonneg _)
    (projectedBatchIterate_energy_le X y ε q hcontract wstar w₀ hfixed)
    hbound

/-- The deterministic iterates converge coordinatewise, hence in the finite product
topology, to the fixed point. -/
theorem projectedBatchIterate_tendsto
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε q : ℝ) (hcontract : BatchLinearContraction X ε q)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (wstar w₀ : Fin n → ℝ)
    (hfixed : projectedBatchStep X y ε wstar = wstar) :
    Filter.Tendsto (projectedBatchIterate X y ε w₀)
      Filter.atTop (nhds wstar) := by
  rw [tendsto_pi_nhds]
  intro i
  have henergy := projectedBatchIterate_energy_tendsto_zero
    X y ε q hcontract hq0 hq1 wstar w₀ hfixed
  have hsqrt : Filter.Tendsto (fun k =>
      √(coefficientEnergy (projectedBatchIterate X y ε w₀ k - wstar)))
      Filter.atTop (nhds 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp henergy
    change Filter.Tendsto (fun k =>
      √(coefficientEnergy (projectedBatchIterate X y ε w₀ k - wstar)))
      Filter.atTop (nhds (√(0 : ℝ))) at hs
    simpa using hs
  have hneg : Filter.Tendsto (fun k =>
      -√(coefficientEnergy (projectedBatchIterate X y ε w₀ k - wstar)))
      Filter.atTop (nhds 0) := by
    simpa only [neg_zero] using hsqrt.neg
  have hd : Filter.Tendsto (fun k =>
      projectedBatchIterate X y ε w₀ k i - wstar i)
      Filter.atTop (nhds 0) := by
    apply hneg.squeeze hsqrt
    · intro k
      have hsingle :
          (projectedBatchIterate X y ε w₀ k i - wstar i) ^ 2 ≤
            coefficientEnergy (projectedBatchIterate X y ε w₀ k - wstar) := by
        unfold coefficientEnergy
        exact Finset.single_le_sum
          (fun j _ => sq_nonneg ((projectedBatchIterate X y ε w₀ k - wstar) j))
          (Finset.mem_univ i)
      have habs : |projectedBatchIterate X y ε w₀ k i - wstar i| ≤
          √(coefficientEnergy (projectedBatchIterate X y ε w₀ k - wstar)) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hsingle
      exact (abs_le.mp habs).1
    · intro k
      have hsingle :
          (projectedBatchIterate X y ε w₀ k i - wstar i) ^ 2 ≤
            coefficientEnergy (projectedBatchIterate X y ε w₀ k - wstar) := by
        unfold coefficientEnergy
        exact Finset.single_le_sum
          (fun j _ => sq_nonneg ((projectedBatchIterate X y ε w₀ k - wstar) j))
          (Finset.mem_univ i)
      have habs : |projectedBatchIterate X y ε w₀ k i - wstar i| ≤
          √(coefficientEnergy (projectedBatchIterate X y ε w₀ k - wstar)) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hsingle
      exact (abs_le.mp habs).2
  have hc : Filter.Tendsto (fun _ : ℕ => wstar i)
      Filter.atTop (nhds (wstar i)) := tendsto_const_nhds
  have hadd := hd.add hc
  simpa only [sub_add_cancel, zero_add] using hadd

/-- Deterministic projected batch-gradient convergence to any NNLS minimizer under a
positive step and the explicit spectral contraction hypothesis. -/
theorem projectedBatchIterate_tendsto_nnlsMinimizer
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε q : ℝ) (hε : 0 < ε)
    (hcontract : BatchLinearContraction X ε q)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (wstar w₀ : Fin n → ℝ)
    (hstar : IsNNLSMinimizer X y wstar) :
    Filter.Tendsto (projectedBatchIterate X y ε w₀)
      Filter.atTop (nhds wstar) := by
  have hfixed : projectedBatchStep X y ε wstar = wstar :=
    (projectedBatchStep_fixed_iff_nnlsMinimizer X y hε wstar).mpr hstar
  exact projectedBatchIterate_tendsto X y ε q hcontract hq0 hq1
    wstar w₀ hfixed

end

end IPNPCNS
