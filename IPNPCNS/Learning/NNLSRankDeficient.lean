import IPNPCNS.Learning.NNLSSpectral
import Mathlib.Topology.Sequences

/-!
# Rank-deficient deterministic NNLS convergence

This module removes the positive lower singular-value hypothesis from deterministic
projected-gradient convergence.  An upper Gram bound and the open step interval
`0 < ε < 2 / L` give Fejér descent.  Finite-dimensional compactness then selects a
coefficient minimizer even when the minimizer is not unique.
-/

open scoped BigOperators

namespace IPNPCNS

noncomputable section

variable {n N : ℕ}

/-- The upper spectral information needed in the rank-deficient argument. -/
def DesignUpperBound
    (X : Matrix (Fin n) (Fin N) ℝ) (L : ℝ) : Prop :=
  ∀ z : Fin N → ℝ,
    coefficientEnergy (X.mulVec z) ≤ L * coefficientEnergy z

theorem DesignSpectralBounds.toDesignUpperBound
    {X : Matrix (Fin n) (Fin N) ℝ} {μ L : ℝ}
    (hbounds : DesignSpectralBounds X μ L) :
    DesignUpperBound X L :=
  hbounds.upper

/-- The positive coefficient multiplying prediction error in the Fejér estimate. -/
def rankDeficientDescentCoefficient (ε L : ℝ) : ℝ :=
  ε * (2 - ε * L)

theorem rankDeficientDescentCoefficient_pos
    {ε L : ℝ} (hε : 0 < ε) (hstep : ε * L < 2) :
    0 < rankDeficientDescentCoefficient ε L := by
  exact mul_pos hε (sub_pos.mpr hstep)

/-- An upper Gram bound gives an exact loss of prediction energy for the raw affine
gradient step.  No lower spectral bound occurs here. -/
theorem batchLinearErrorStep_energy_le_upper
    (X : Matrix (Fin n) (Fin N) ℝ) (ε L : ℝ)
    (hupper : DesignUpperBound X L) (h : Fin n → ℝ) :
    coefficientEnergy (batchLinearErrorStep X ε h) ≤
      coefficientEnergy h -
        rankDeficientDescentCoefficient ε L * predictionEnergy X h := by
  rw [coefficientEnergy_batchLinearErrorStep]
  calc
    coefficientEnergy h - 2 * ε * predictionEnergy X h +
        ε ^ 2 * coefficientEnergy (coefficientGramAction X h) ≤
      coefficientEnergy h - 2 * ε * predictionEnergy X h +
        ε ^ 2 * (L * predictionEnergy X h) := by
      gcongr
      exact hupper (nnlsPrediction X h)
    _ = coefficientEnergy h -
        rankDeficientDescentCoefficient ε L * predictionEnergy X h := by
      unfold rankDeficientDescentCoefficient
      ring

/-- Fejér descent of one projected-gradient step relative to any fixed point. -/
theorem projectedBatchStep_fejer_descent
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε L : ℝ) (hupper : DesignUpperBound X L)
    (wstar w : Fin n → ℝ)
    (hfixed : projectedBatchStep X y ε wstar = wstar) :
    coefficientEnergy (projectedBatchStep X y ε w - wstar) +
        rankDeficientDescentCoefficient ε L * predictionEnergy X (w - wstar) ≤
      coefficientEnergy (w - wstar) := by
  have hstep :
      coefficientEnergy (projectedBatchStep X y ε w - wstar) ≤
        coefficientEnergy (w - wstar) -
          rankDeficientDescentCoefficient ε L * predictionEnergy X (w - wstar) := by
    calc
      coefficientEnergy (projectedBatchStep X y ε w - wstar) =
          coefficientEnergy
            (projectedBatchStep X y ε w - projectedBatchStep X y ε wstar) := by
        rw [hfixed]
      _ ≤ coefficientEnergy
          ((w - ε • nnlsGradient X y w) -
            (wstar - ε • nnlsGradient X y wstar)) := by
        rw [projectedBatchStep_eq_positivePart, projectedBatchStep_eq_positivePart]
        exact coefficientEnergy_positivePart_sub_le _ _
      _ = coefficientEnergy (batchLinearErrorStep X ε (w - wstar)) := by
        rw [rawBatchStep_sub]
      _ ≤ coefficientEnergy (w - wstar) -
          rankDeficientDescentCoefficient ε L * predictionEnergy X (w - wstar) :=
        batchLinearErrorStep_energy_le_upper X ε L hupper (w - wstar)
  linarith

/-- Fejér descent along the deterministic iteration. -/
theorem projectedBatchIterate_fejer_descent
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε L : ℝ) (hupper : DesignUpperBound X L)
    (wstar w₀ : Fin n → ℝ)
    (hfixed : projectedBatchStep X y ε wstar = wstar) (k : ℕ) :
    coefficientEnergy (projectedBatchIterate X y ε w₀ (k + 1) - wstar) +
        rankDeficientDescentCoefficient ε L *
          predictionEnergy X (projectedBatchIterate X y ε w₀ k - wstar) ≤
      coefficientEnergy (projectedBatchIterate X y ε w₀ k - wstar) := by
  rw [projectedBatchIterate]
  exact projectedBatchStep_fejer_descent X y ε L hupper wstar _ hfixed

/-- Distances to a fixed point are nonincreasing under a nonnegative descent
coefficient. -/
theorem projectedBatchIterate_energy_antitone
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε L : ℝ) (hupper : DesignUpperBound X L)
    (hc : 0 ≤ rankDeficientDescentCoefficient ε L)
    (wstar w₀ : Fin n → ℝ)
    (hfixed : projectedBatchStep X y ε wstar = wstar) :
    Antitone (fun k =>
      coefficientEnergy (projectedBatchIterate X y ε w₀ k - wstar)) := by
  apply antitone_nat_of_succ_le
  intro k
  have hdesc := projectedBatchIterate_fejer_descent
    X y ε L hupper wstar w₀ hfixed k
  have hnonneg := predictionEnergy_nonneg X
    (projectedBatchIterate X y ε w₀ k - wstar)
  nlinarith

/-- Telescoped Fejér descent controls all partial sums of prediction error. -/
theorem projectedBatchIterate_prediction_partialSum
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε L : ℝ) (hupper : DesignUpperBound X L)
    (wstar w₀ : Fin n → ℝ)
    (hfixed : projectedBatchStep X y ε wstar = wstar) :
    ∀ m,
      (∑ k ∈ Finset.range m,
          rankDeficientDescentCoefficient ε L *
            predictionEnergy X (projectedBatchIterate X y ε w₀ k - wstar)) +
          coefficientEnergy (projectedBatchIterate X y ε w₀ m - wstar) ≤
        coefficientEnergy (w₀ - wstar) := by
  intro m
  induction m with
  | zero => simp [projectedBatchIterate]
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hdesc := projectedBatchIterate_fejer_descent
        X y ε L hupper wstar w₀ hfixed m
      linarith

/-- The prediction errors are summable after multiplication by the positive Fejér
coefficient. -/
theorem projectedBatchIterate_scaledPrediction_summable
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε L : ℝ) (hupper : DesignUpperBound X L)
    (hc : 0 ≤ rankDeficientDescentCoefficient ε L)
    (wstar w₀ : Fin n → ℝ)
    (hfixed : projectedBatchStep X y ε wstar = wstar) :
    Summable (fun k =>
      rankDeficientDescentCoefficient ε L *
        predictionEnergy X (projectedBatchIterate X y ε w₀ k - wstar)) := by
  apply summable_of_sum_range_le
  · intro k
    exact mul_nonneg hc (predictionEnergy_nonneg X _)
  · intro m
    have hpartial := projectedBatchIterate_prediction_partialSum
      X y ε L hupper wstar w₀ hfixed m
    nlinarith [coefficientEnergy_nonneg
      (projectedBatchIterate X y ε w₀ m - wstar)]

/-- Under the open step interval, the prediction error tends to zero even if
coefficient error cannot do so relative to an arbitrarily chosen minimizer. -/
theorem projectedBatchIterate_predictionEnergy_tendsto_zero
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε L : ℝ) (hupper : DesignUpperBound X L)
    (hc : 0 < rankDeficientDescentCoefficient ε L)
    (wstar w₀ : Fin n → ℝ)
    (hfixed : projectedBatchStep X y ε wstar = wstar) :
    Filter.Tendsto (fun k =>
      predictionEnergy X (projectedBatchIterate X y ε w₀ k - wstar))
      Filter.atTop (nhds 0) := by
  have hscaled := (projectedBatchIterate_scaledPrediction_summable
    X y ε L hupper hc.le wstar w₀ hfixed).tendsto_atTop_zero
  have hdiv := hscaled.div_const (rankDeficientDescentCoefficient ε L)
  convert hdiv using 1 <;> simp [hc.ne']

/-- Squared Euclidean coefficient energy is continuous in the finite product
topology. -/
theorem continuous_coefficientEnergy (n : ℕ) :
    Continuous (coefficientEnergy : (Fin n → ℝ) → ℝ) := by
  unfold coefficientEnergy
  fun_prop

/-- Squared prediction energy is continuous in the finite product topology. -/
theorem continuous_predictionEnergy
    (X : Matrix (Fin n) (Fin N) ℝ) :
    Continuous (predictionEnergy X) := by
  unfold predictionEnergy coefficientEnergy nnlsPrediction Matrix.mulVec dotProduct
  fun_prop

theorem continuous_coefficientEnergy_sub (z : Fin n → ℝ) :
    Continuous (fun w => coefficientEnergy (w - z)) :=
  (continuous_coefficientEnergy n).comp (continuous_id.sub continuous_const)

theorem continuous_predictionEnergy_sub
    (X : Matrix (Fin n) (Fin N) ℝ) (z : Fin n → ℝ) :
    Continuous (fun w => predictionEnergy X (w - z)) :=
  (continuous_predictionEnergy X).comp (continuous_id.sub continuous_const)

/-- Vanishing finite Euclidean energy is enough for convergence in the coefficient
product topology. -/
theorem tendsto_of_coefficientEnergy_sub_tendsto_zero
    (u : ℕ → (Fin n → ℝ)) (z : Fin n → ℝ)
    (henergy : Filter.Tendsto (fun k => coefficientEnergy (u k - z))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto u Filter.atTop (nhds z) := by
  rw [tendsto_pi_nhds]
  intro i
  have hsqrt : Filter.Tendsto (fun k => √(coefficientEnergy (u k - z)))
      Filter.atTop (nhds 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp henergy
    change Filter.Tendsto (fun k => √(coefficientEnergy (u k - z)))
      Filter.atTop (nhds (√(0 : ℝ))) at hs
    simpa using hs
  have hneg : Filter.Tendsto (fun k => -√(coefficientEnergy (u k - z)))
      Filter.atTop (nhds 0) := by
    simpa only [neg_zero] using hsqrt.neg
  have hd : Filter.Tendsto (fun k => u k i - z i)
      Filter.atTop (nhds 0) := by
    apply hneg.squeeze hsqrt
    · intro k
      have hsingle : (u k i - z i) ^ 2 ≤ coefficientEnergy (u k - z) := by
        unfold coefficientEnergy
        exact Finset.single_le_sum
          (fun j _ => sq_nonneg ((u k - z) j)) (Finset.mem_univ i)
      have habs : |u k i - z i| ≤ √(coefficientEnergy (u k - z)) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hsingle
      exact (abs_le.mp habs).1
    · intro k
      have hsingle : (u k i - z i) ^ 2 ≤ coefficientEnergy (u k - z) := by
        unfold coefficientEnergy
        exact Finset.single_le_sum
          (fun j _ => sq_nonneg ((u k - z) j)) (Finset.mem_univ i)
      have habs : |u k i - z i| ≤ √(coefficientEnergy (u k - z)) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hsingle
      exact (abs_le.mp habs).2
  have hc : Filter.Tendsto (fun _ : ℕ => z i)
      Filter.atTop (nhds (z i)) := tendsto_const_nhds
  have hadd := hd.add hc
  simpa only [sub_add_cancel, zero_add] using hadd

/-- Every tail iterate lies in the nonnegative orthant. -/
theorem projectedBatchIterate_nonnegative_succ
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε : ℝ) (w₀ : Fin n → ℝ) (k : ℕ) :
    IsNonnegative (projectedBatchIterate X y ε w₀ (k + 1)) := by
  rw [projectedBatchIterate]
  exact projectedBatchStep_nonnegative X y ε _

/-- Feasibility plus the prediction of a known minimizer is sufficient for NNLS
optimality. -/
theorem nnlsMinimizer_of_prediction_eq
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    {wstar w : Fin n → ℝ} (hstar : IsNNLSMinimizer X y wstar)
    (hw : IsNonnegative w)
    (hprediction : nnlsPrediction X w = nnlsPrediction X wstar) :
    IsNNLSMinimizer X y w := by
  refine ⟨hw, ?_⟩
  intro v hv
  calc
    nnlsLoss X y w = nnlsLoss X y wstar := by
      unfold nnlsLoss
      rw [hprediction]
    _ ≤ nnlsLoss X y v := hstar.2 v hv

/-- A coordinate difference is controlled by the square root of total coefficient
energy. -/
theorem abs_coordinate_sub_le_sqrt_coefficientEnergy
    (u z : Fin n → ℝ) (i : Fin n) :
    |u i - z i| ≤ √(coefficientEnergy (u - z)) := by
  have hsingle : (u i - z i) ^ 2 ≤ coefficientEnergy (u - z) := by
    unfold coefficientEnergy
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg ((u - z) j)) (Finset.mem_univ i)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsingle

/-- Finite-dimensional Fejér convergence with no lower singular-value bound.  The
conclusion selects a minimizer, proves convergence to it, records asymptotic
regularity, and identifies its prediction with that of the supplied witness. -/
theorem projectedBatchIterate_tendsto_some_nnlsMinimizer_of_positive_descent
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε L : ℝ) (hupper : DesignUpperBound X L)
    (hε : 0 < ε) (hc : 0 < rankDeficientDescentCoefficient ε L)
    (wstar w₀ : Fin n → ℝ) (hstar : IsNNLSMinimizer X y wstar) :
    ∃ winfinity : Fin n → ℝ,
      IsNNLSMinimizer X y winfinity ∧
      Filter.Tendsto (projectedBatchIterate X y ε w₀)
        Filter.atTop (nhds winfinity) ∧
      Filter.Tendsto (fun k =>
        projectedBatchIterate X y ε w₀ (k + 1) -
          projectedBatchIterate X y ε w₀ k)
        Filter.atTop (nhds 0) ∧
      nnlsPrediction X winfinity = nnlsPrediction X wstar := by
  let u : ℕ → (Fin n → ℝ) := projectedBatchIterate X y ε w₀
  let radius : ℝ := √(coefficientEnergy (w₀ - wstar))
  let K : Set (Fin n → ℝ) := Set.univ.pi fun i =>
    Set.Icc (wstar i - radius) (wstar i + radius)
  have hfixed : projectedBatchStep X y ε wstar = wstar :=
    (projectedBatchStep_fixed_iff_nnlsMinimizer X y hε wstar).mpr hstar
  have hanti : Antitone (fun k => coefficientEnergy (u k - wstar)) := by
    simpa only [u] using projectedBatchIterate_energy_antitone
      X y ε L hupper hc.le wstar w₀ hfixed
  have hbound : ∀ k, coefficientEnergy (u k - wstar) ≤
      coefficientEnergy (w₀ - wstar) := by
    intro k
    have hk := hanti (Nat.zero_le k)
    simpa [u, projectedBatchIterate] using hk
  have hKcompact : IsCompact K := by
    dsimp only [K]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hKmem : ∀ k, u (k + 1) ∈ K := by
    intro k
    rw [Set.mem_pi]
    intro i hi
    have habs0 := abs_coordinate_sub_le_sqrt_coefficientEnergy
      (u (k + 1)) wstar i
    have habs : |u (k + 1) i - wstar i| ≤ radius := by
      exact habs0.trans (Real.sqrt_le_sqrt (hbound (k + 1)))
    rcases abs_le.mp habs with ⟨hlower, hupper'⟩
    constructor <;> dsimp only [radius] <;> linarith
  rcases hKcompact.tendsto_subseq (x := fun k => u (k + 1)) hKmem with
    ⟨winfinity, hwinfinityK, φ, hφ, hsubsequence⟩
  have hwinfinity_nonnegative : IsNonnegative winfinity := by
    intro i
    have hcoordinate : Filter.Tendsto (fun k => u (φ k + 1) i)
        Filter.atTop (nhds (winfinity i)) := by
      have hi := (tendsto_pi_nhds.mp hsubsequence) i
      simpa only [Function.comp_apply] using hi
    apply ge_of_tendsto hcoordinate
    exact Filter.Eventually.of_forall fun k => by
      simpa only [u] using
        projectedBatchIterate_nonnegative_succ X y ε w₀ (φ k) i
  have hindex : Filter.Tendsto (fun k => φ k + 1)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
  have hpredictionWhole : Filter.Tendsto (fun k =>
      predictionEnergy X (u k - wstar)) Filter.atTop (nhds 0) := by
    simpa only [u] using projectedBatchIterate_predictionEnergy_tendsto_zero
      X y ε L hupper hc wstar w₀ hfixed
  have hpredictionSubsequenceZero : Filter.Tendsto (fun k =>
      predictionEnergy X (u (φ k + 1) - wstar)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def] using hpredictionWhole.comp hindex
  have hpredictionSubsequenceLimit : Filter.Tendsto (fun k =>
      predictionEnergy X (u (φ k + 1) - wstar)) Filter.atTop
      (nhds (predictionEnergy X (winfinity - wstar))) := by
    have hcontinuous := (continuous_predictionEnergy_sub X wstar).tendsto winfinity
    simpa only [Function.comp_def] using hcontinuous.comp hsubsequence
  have hpredictionEnergyZero : predictionEnergy X (winfinity - wstar) = 0 :=
    tendsto_nhds_unique hpredictionSubsequenceLimit hpredictionSubsequenceZero
  have hpredictionDirect :
      nnlsPrediction X winfinity = nnlsPrediction X wstar := by
    have hzero : nnlsPrediction X (winfinity - wstar) = 0 := by
      apply (coefficientEnergy_eq_zero_iff
        (nnlsPrediction X (winfinity - wstar))).mp
      simpa only [predictionEnergy] using hpredictionEnergyZero
    rw [nnlsPrediction_sub] at hzero
    exact sub_eq_zero.mp hzero
  have hwinfinityMinimizer : IsNNLSMinimizer X y winfinity :=
    nnlsMinimizer_of_prediction_eq X y hstar hwinfinity_nonnegative hpredictionDirect
  have hcommonPrediction :
      nnlsPrediction X winfinity = nnlsPrediction X wstar :=
    nnlsMinimizers_prediction_eq X y hwinfinityMinimizer hstar
  have hfixedInfinity : projectedBatchStep X y ε winfinity = winfinity :=
    (projectedBatchStep_fixed_iff_nnlsMinimizer X y hε winfinity).mpr
      hwinfinityMinimizer
  have hantiInfinity : Antitone (fun k =>
      coefficientEnergy (u k - winfinity)) := by
    simpa only [u] using projectedBatchIterate_energy_antitone
      X y ε L hupper hc.le winfinity w₀ hfixedInfinity
  have henergySubsequence : Filter.Tendsto (fun k =>
      coefficientEnergy (u (φ k + 1) - winfinity)) Filter.atTop (nhds 0) := by
    have hcontinuous :=
      (continuous_coefficientEnergy_sub winfinity).tendsto winfinity
    have hlimit := hcontinuous.comp hsubsequence
    simpa only [Function.comp_def, sub_self,
      (coefficientEnergy_eq_zero_iff (0 : Fin n → ℝ)).mpr rfl] using hlimit
  have henergy : Filter.Tendsto (fun k =>
      coefficientEnergy (u k - winfinity)) Filter.atTop (nhds 0) := by
    apply (tendsto_iff_tendsto_subseq_of_antitone hantiInfinity hindex).mpr
    simpa only [Function.comp_def] using henergySubsequence
  have hconvergence : Filter.Tendsto u Filter.atTop (nhds winfinity) :=
    tendsto_of_coefficientEnergy_sub_tendsto_zero u winfinity henergy
  have htail : Filter.Tendsto (fun k => u (k + 1))
      Filter.atTop (nhds winfinity) :=
    hconvergence.comp (Filter.tendsto_add_atTop_nat 1)
  have hasymptotic : Filter.Tendsto (fun k => u (k + 1) - u k)
      Filter.atTop (nhds 0) := by
    simpa only [sub_self] using htail.sub hconvergence
  exact ⟨winfinity, hwinfinityMinimizer, by simpa only [u] using hconvergence,
    by simpa only [u] using hasymptotic, hcommonPrediction⟩

/-- Paper-facing rank-deficient convergence theorem under the open interval
`0 < ε < 2 / L`.  Its assumptions contain no positive lower singular-value bound. -/
theorem projectedBatchIterate_tendsto_some_nnlsMinimizer_of_upperBound
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε L : ℝ) (hupper : DesignUpperBound X L)
    (hL : 0 < L) (hε : 0 < ε) (hstep : ε < 2 / L)
    (wstar w₀ : Fin n → ℝ) (hstar : IsNNLSMinimizer X y wstar) :
    ∃ winfinity : Fin n → ℝ,
      IsNNLSMinimizer X y winfinity ∧
      Filter.Tendsto (projectedBatchIterate X y ε w₀)
        Filter.atTop (nhds winfinity) ∧
      Filter.Tendsto (fun k =>
        projectedBatchIterate X y ε w₀ (k + 1) -
          projectedBatchIterate X y ε w₀ k)
        Filter.atTop (nhds 0) ∧
      nnlsPrediction X winfinity = nnlsPrediction X wstar := by
  have hεL : ε * L < 2 := (lt_div_iff₀ hL).mp hstep
  exact projectedBatchIterate_tendsto_some_nnlsMinimizer_of_positive_descent
    X y ε L hupper hε
      (rankDeficientDescentCoefficient_pos hε hεL) wstar w₀ hstar

/-- Set-nonemptiness form of the rank-deficient convergence theorem. -/
theorem projectedBatchIterate_tendsto_some_nnlsMinimizer_of_upperBound_of_exists
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε L : ℝ) (hupper : DesignUpperBound X L)
    (hL : 0 < L) (hε : 0 < ε) (hstep : ε < 2 / L)
    (w₀ : Fin n → ℝ)
    (hsolution : ∃ wstar, IsNNLSMinimizer X y wstar) :
    ∃ winfinity : Fin n → ℝ,
      IsNNLSMinimizer X y winfinity ∧
      Filter.Tendsto (projectedBatchIterate X y ε w₀)
        Filter.atTop (nhds winfinity) ∧
      Filter.Tendsto (fun k =>
        projectedBatchIterate X y ε w₀ (k + 1) -
          projectedBatchIterate X y ε w₀ k)
        Filter.atTop (nhds 0) := by
  rcases hsolution with ⟨wstar, hstar⟩
  rcases projectedBatchIterate_tendsto_some_nnlsMinimizer_of_upperBound
      X y ε L hupper hL hε hstep wstar w₀ hstar with
    ⟨winfinity, hminimizer, hconvergence, hasymptotic, _hprediction⟩
  exact ⟨winfinity, hminimizer, hconvergence, hasymptotic⟩

/-- Prediction injectivity turns the selected rank-deficient limit into the specified
minimizer.  Without this hypothesis the preceding theorem deliberately asserts only
convergence to some minimizer. -/
theorem projectedBatchIterate_tendsto_nnlsMinimizer_of_upperBound_of_injective
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (ε L : ℝ) (hupper : DesignUpperBound X L)
    (hL : 0 < L) (hε : 0 < ε) (hstep : ε < 2 / L)
    (hinjective : Function.Injective (nnlsPrediction X))
    (wstar w₀ : Fin n → ℝ) (hstar : IsNNLSMinimizer X y wstar) :
    Filter.Tendsto (projectedBatchIterate X y ε w₀)
      Filter.atTop (nhds wstar) := by
  rcases projectedBatchIterate_tendsto_some_nnlsMinimizer_of_upperBound
      X y ε L hupper hL hε hstep wstar w₀ hstar with
    ⟨winfinity, hminimizer, hconvergence, _hasymptotic, hprediction⟩
  have heq : winfinity = wstar := hinjective hprediction
  simpa only [heq] using hconvergence

end

end IPNPCNS
