import IPNPCNS.Learning.NNLSConvergence

/-!
# Spectral sufficient conditions for deterministic NNLS convergence

This module derives the explicit contraction hypothesis used in
`NNLSConvergence.lean` from lower and upper squared singular-value bounds for the
finite design matrix.  It also records exactly what fails in the rank-deficient case.
-/

open scoped BigOperators

namespace IPNPCNS

noncomputable section

variable {n N : ℕ}

/-- Squared prediction norm `‖Xᵀh‖₂²`. -/
def predictionEnergy (X : Matrix (Fin n) (Fin N) ℝ) (h : Fin n → ℝ) : ℝ :=
  coefficientEnergy (nnlsPrediction X h)

/-- The coefficient Gram action `(X Xᵀ)h` for the paper's `Xᵀh` convention. -/
def coefficientGramAction
    (X : Matrix (Fin n) (Fin N) ℝ) (h : Fin n → ℝ) : Fin n → ℝ :=
  X.mulVec (nnlsPrediction X h)

/-- The explicit matrix orientation of the coefficient Gram operator is `X Xᵀ`. -/
theorem coefficientGramAction_eq_mulVec
    (X : Matrix (Fin n) (Fin N) ℝ) (h : Fin n → ℝ) :
    coefficientGramAction X h = (X * X.transpose).mulVec h := by
  simp [coefficientGramAction, nnlsPrediction, Matrix.mulVec_mulVec]

theorem predictionEnergy_nonneg
    (X : Matrix (Fin n) (Fin N) ℝ) (h : Fin n → ℝ) :
    0 ≤ predictionEnergy X h :=
  coefficientEnergy_nonneg _

theorem coefficientDot_self (h : Fin n → ℝ) :
    coefficientDot h h = coefficientEnergy h := by
  simp [coefficientDot, coefficientEnergy, pow_two]

theorem coefficientDot_comm (u v : Fin n → ℝ) :
    coefficientDot u v = coefficientDot v u := by
  unfold coefficientDot
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The Gram quadratic form is exactly the squared prediction norm. -/
theorem coefficientDot_gramAction
    (X : Matrix (Fin n) (Fin N) ℝ) (h : Fin n → ℝ) :
    coefficientDot h (coefficientGramAction X h) = predictionEnergy X h := by
  rw [coefficientDot_comm]
  simpa [coefficientGramAction, predictionEnergy, coefficientEnergy, nnlsGradient,
    pow_two]
    using coefficientDot_nnlsGradient X (0 : Fin N → ℝ) h h

/-- Exact energy expansion for one unprojected Gram step. -/
theorem coefficientEnergy_batchLinearErrorStep
    (X : Matrix (Fin n) (Fin N) ℝ) (ε : ℝ) (h : Fin n → ℝ) :
    coefficientEnergy (batchLinearErrorStep X ε h) =
      coefficientEnergy h - 2 * ε * predictionEnergy X h +
        ε ^ 2 * coefficientEnergy (coefficientGramAction X h) := by
  let g := coefficientGramAction X h
  calc
    coefficientEnergy (batchLinearErrorStep X ε h) =
        ∑ i, (h i - ε * g i) ^ 2 := by
      simp only [coefficientEnergy, batchLinearErrorStep, coefficientGramAction, g,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    _ = ∑ i, (h i ^ 2 - 2 * ε * (h i * g i) + ε ^ 2 * g i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = coefficientEnergy h - 2 * ε * coefficientDot h g +
        ε ^ 2 * coefficientEnergy g := by
      simp only [coefficientEnergy, coefficientDot, Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = coefficientEnergy h - 2 * ε * predictionEnergy X h +
        ε ^ 2 * coefficientEnergy (coefficientGramAction X h) := by
      rw [coefficientDot_gramAction]

/-- Explicit lower and upper squared singular-value bounds.  `lower` controls
`Xᵀ`, while `upper` controls `X`; for real matrices these use the same nonzero
singular values. -/
structure DesignSpectralBounds
    (X : Matrix (Fin n) (Fin N) ℝ) (μ L : ℝ) : Prop where
  lower : ∀ h, μ * coefficientEnergy h ≤ predictionEnergy X h
  upper : ∀ z : Fin N → ℝ,
    coefficientEnergy (X.mulVec z) ≤ L * coefficientEnergy z

theorem DesignSpectralBounds.gramAction_upper
    {X : Matrix (Fin n) (Fin N) ℝ} {μ L : ℝ}
    (hbounds : DesignSpectralBounds X μ L) (h : Fin n → ℝ) :
    coefficientEnergy (coefficientGramAction X h) ≤
      L * predictionEnergy X h := by
  exact hbounds.upper (nnlsPrediction X h)

/-- The squared contraction factor obtained from the interval
`0 < ε < 2 / L`. -/
def gramContractionSquared (ε μ L : ℝ) : ℝ :=
  1 - ε * (2 - ε * L) * μ

def gramContractionFactor (ε μ L : ℝ) : ℝ :=
  Real.sqrt (gramContractionSquared ε μ L)

/-- Spectral energy estimate before taking a square root. -/
theorem batchLinearErrorStep_energy_le_spectral
    (X : Matrix (Fin n) (Fin N) ℝ) (ε μ L : ℝ)
    (hbounds : DesignSpectralBounds X μ L)
    (hε : 0 ≤ ε) (hstep : ε * L ≤ 2)
    (h : Fin n → ℝ) :
    coefficientEnergy (batchLinearErrorStep X ε h) ≤
      gramContractionSquared ε μ L * coefficientEnergy h := by
  have hc : 0 ≤ ε * (2 - ε * L) :=
    mul_nonneg hε (sub_nonneg.mpr hstep)
  rw [coefficientEnergy_batchLinearErrorStep]
  calc
    coefficientEnergy h - 2 * ε * predictionEnergy X h +
        ε ^ 2 * coefficientEnergy (coefficientGramAction X h) ≤
      coefficientEnergy h - 2 * ε * predictionEnergy X h +
        ε ^ 2 * (L * predictionEnergy X h) := by
      gcongr
      exact hbounds.gramAction_upper h
    _ = coefficientEnergy h -
        (ε * (2 - ε * L)) * predictionEnergy X h := by ring
    _ ≤ coefficientEnergy h -
        (ε * (2 - ε * L)) * (μ * coefficientEnergy h) := by
      exact sub_le_sub_left (mul_le_mul_of_nonneg_left (hbounds.lower h) hc) _
    _ = gramContractionSquared ε μ L * coefficientEnergy h := by
      unfold gramContractionSquared
      ring

private theorem gramContractionSquared_nonneg
    {ε μ L : ℝ} (_hL : 0 < L) (hμL : μ ≤ L)
    (hε : 0 < ε) (hstep : ε * L < 2) :
    0 ≤ gramContractionSquared ε μ L := by
  have hc : 0 ≤ ε * (2 - ε * L) :=
    mul_nonneg hε.le (sub_nonneg.mpr hstep.le)
  have hμbound :
      ε * (2 - ε * L) * μ ≤ ε * (2 - ε * L) * L :=
    mul_le_mul_of_nonneg_left hμL hc
  have hsquare := sq_nonneg (ε * L - 1)
  have hLbound : ε * (2 - ε * L) * L ≤ 1 := by
    nlinarith
  unfold gramContractionSquared
  linarith

theorem gramContractionFactor_nonneg
    (ε μ L : ℝ) : 0 ≤ gramContractionFactor ε μ L :=
  Real.sqrt_nonneg _

theorem gramContractionFactor_lt_one
    {ε μ L : ℝ} (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hε : 0 < ε) (hstep : ε * L < 2) :
    gramContractionFactor ε μ L < 1 := by
  have hsq0 := gramContractionSquared_nonneg hL hμL hε hstep
  have hcpos : 0 < ε * (2 - ε * L) :=
    mul_pos hε (sub_pos.mpr hstep)
  have hsq1 : gramContractionSquared ε μ L < 1 := by
    unfold gramContractionSquared
    nlinarith [mul_pos hcpos hμ]
  simpa [gramContractionFactor] using
    (Real.sqrt_lt_sqrt hsq0 hsq1 :
      Real.sqrt (gramContractionSquared ε μ L) < Real.sqrt 1)

/-- Lower/upper singular-value bounds imply T-0008's exact contraction interface. -/
theorem batchLinearContraction_of_designSpectralBounds
    (X : Matrix (Fin n) (Fin N) ℝ) (ε μ L : ℝ)
    (hbounds : DesignSpectralBounds X μ L)
    (hL : 0 < L) (hμL : μ ≤ L)
    (hε : 0 < ε) (hstep : ε * L < 2) :
    BatchLinearContraction X ε (gramContractionFactor ε μ L) := by
  intro h
  have hsq0 := gramContractionSquared_nonneg hL hμL hε hstep
  calc
    coefficientEnergy (batchLinearErrorStep X ε h) ≤
        gramContractionSquared ε μ L * coefficientEnergy h :=
      batchLinearErrorStep_energy_le_spectral X ε μ L hbounds hε.le hstep.le h
    _ = gramContractionFactor ε μ L ^ 2 * coefficientEnergy h := by
      rw [gramContractionFactor, Real.sq_sqrt hsq0]

/-- Paper-facing form of the step interval `0 < ε < 2 / L`. -/
theorem batchLinearContraction_of_step_lt_two_div
    (X : Matrix (Fin n) (Fin N) ℝ) (ε μ L : ℝ)
    (hbounds : DesignSpectralBounds X μ L)
    (hL : 0 < L) (hμL : μ ≤ L)
    (hε : 0 < ε) (hstep : ε < 2 / L) :
    BatchLinearContraction X ε (gramContractionFactor ε μ L) := by
  apply batchLinearContraction_of_designSpectralBounds X ε μ L hbounds hL hμL hε
  exact (lt_div_iff₀ hL).mp hstep

theorem coefficientEnergy_eq_zero_iff (h : Fin n → ℝ) :
    coefficientEnergy h = 0 ↔ h = 0 := by
  constructor
  · intro hzero
    funext i
    have hi : h i ^ 2 ≤ coefficientEnergy h := by
      unfold coefficientEnergy
      exact Finset.single_le_sum (fun j _ => sq_nonneg (h j)) (Finset.mem_univ i)
    have hisq : h i ^ 2 = 0 := le_antisymm (by simpa [hzero] using hi) (sq_nonneg _)
    exact sq_eq_zero_iff.mp hisq
  · rintro rfl
    simp [coefficientEnergy]

theorem coefficientEnergy_pos_iff (h : Fin n → ℝ) :
    0 < coefficientEnergy h ↔ h ≠ 0 := by
  constructor
  · intro hpos hzero
    exact (ne_of_gt hpos) ((coefficientEnergy_eq_zero_iff h).mpr hzero)
  · intro hne
    apply lt_of_le_of_ne (coefficientEnergy_nonneg h)
    intro hzero
    exact hne ((coefficientEnergy_eq_zero_iff h).mp hzero.symm)

/-- Positive lower singular-value control makes `Xᵀ` injective. -/
theorem nnlsPrediction_injective_of_lower
    {X : Matrix (Fin n) (Fin N) ℝ} {μ L : ℝ}
    (hbounds : DesignSpectralBounds X μ L) (hμ : 0 < μ) :
    Function.Injective (nnlsPrediction X) := by
  intro u v huv
  have hpred : nnlsPrediction X (u - v) = 0 := by
    rw [nnlsPrediction_sub, huv]
    simp
  have hlower := hbounds.lower (u - v)
  change μ * coefficientEnergy (u - v) ≤
    coefficientEnergy (nnlsPrediction X (u - v)) at hlower
  rw [hpred] at hlower
  have henergy : coefficientEnergy (u - v) = 0 := by
    have hlower0 : μ * coefficientEnergy (u - v) ≤ 0 := by
      simpa [coefficientEnergy] using hlower
    have hnonneg := coefficientEnergy_nonneg (u - v)
    apply le_antisymm ?_ hnonneg
    by_contra hnot
    have hpos : 0 < coefficientEnergy (u - v) := lt_of_not_ge hnot
    linarith [mul_pos hμ hpos]
  exact sub_eq_zero.mp ((coefficientEnergy_eq_zero_iff (u - v)).mp henergy)

/-- Even without coefficient uniqueness, any two NNLS minimizers have the same
prediction. -/
theorem nnlsMinimizers_prediction_eq
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    {w v : Fin n → ℝ}
    (hw : IsNNLSMinimizer X y w) (hv : IsNNLSMinimizer X y v) :
    nnlsPrediction X w = nnlsPrediction X v := by
  have hloss : nnlsLoss X y w = nnlsLoss X y v :=
    le_antisymm (hw.2 v hv.1) (hv.2 w hw.1)
  have hfirst := nnls_firstOrder_nonneg_of_minimizer X y hw hv.1
  have hexpand := nnlsLoss_add X y w (v - w)
  have hadd : w + (v - w) = v := by
    funext i
    simp
  rw [hadd, hloss] at hexpand
  have hpredEnergy : predictionEnergy X (v - w) = 0 := by
    unfold predictionEnergy coefficientEnergy
    have hsum : 0 ≤ ∑ j, nnlsPrediction X (v - w) j ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    nlinarith
  have hpredZero : nnlsPrediction X (v - w) = 0 := by
    apply (coefficientEnergy_eq_zero_iff (nnlsPrediction X (v - w))).mp
    exact hpredEnergy
  rw [nnlsPrediction_sub] at hpredZero
  exact sub_eq_zero.mp hpredZero |>.symm

/-- Full row rank, witnessed by a positive lower singular-value bound, makes the NNLS
coefficient minimizer unique. -/
theorem nnlsMinimizer_unique_of_designSpectralBounds
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ) {μ L : ℝ}
    (hbounds : DesignSpectralBounds X μ L) (hμ : 0 < μ)
    {w v : Fin n → ℝ}
    (hw : IsNNLSMinimizer X y w) (hv : IsNNLSMinimizer X y v) :
    w = v := by
  exact nnlsPrediction_injective_of_lower hbounds hμ
    (nnlsMinimizers_prediction_eq X y hw hv)

/-- T-0008 instantiated with explicit finite singular-value and step-size bounds. -/
theorem projectedBatchIterate_tendsto_of_designSpectralBounds
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε μ L : ℝ) (hbounds : DesignSpectralBounds X μ L)
    (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hε : 0 < ε) (hstep : ε < 2 / L)
    (wstar w₀ : Fin n → ℝ) (hstar : IsNNLSMinimizer X y wstar) :
    Filter.Tendsto (projectedBatchIterate X y ε w₀)
      Filter.atTop (nhds wstar) := by
  let q := gramContractionFactor ε μ L
  have hεL : ε * L < 2 := (lt_div_iff₀ hL).mp hstep
  have hcontract : BatchLinearContraction X ε q :=
    batchLinearContraction_of_designSpectralBounds X ε μ L hbounds hL hμL hε hεL
  exact projectedBatchIterate_tendsto_nnlsMinimizer X y ε q hε hcontract
    (gramContractionFactor_nonneg ε μ L)
    (gramContractionFactor_lt_one hL hμ hμL hε hεL)
    wstar w₀ hstar

/-- A nonzero prediction-kernel direction rules out every strict
coefficient-space contraction factor. -/
theorem no_strict_batchLinearContraction_of_prediction_kernel
    (X : Matrix (Fin n) (Fin N) ℝ) (ε q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    {h : Fin n → ℝ} (hne : h ≠ 0) (hker : nnlsPrediction X h = 0) :
    ¬BatchLinearContraction X ε q := by
  intro hcontract
  have hstep : batchLinearErrorStep X ε h = h := by
    unfold batchLinearErrorStep
    rw [hker]
    simp
  have hbound := hcontract h
  rw [hstep] at hbound
  have henergy : 0 < coefficientEnergy h :=
    (coefficientEnergy_pos_iff h).mpr hne
  have hq2 : q ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hq1) (by linarith : 0 < 1 + q)]
  nlinarith

end

end IPNPCNS
