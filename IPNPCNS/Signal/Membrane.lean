import IPNPCNS.Signal.Deterministic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set
open scoped Interval NNReal

/-!
# Exact membrane step and quadratic frozen-drive error

This file gives equation (33) a concrete analytic interpretation. The exact
first-order low-pass response is written as an exponentially weighted Bochner
integral. Freezing a Lipschitz net drive at the beginning of a nonnegative step
produces the paper's displayed update, and the remaining integral has norm at most
`(L / τ) |Δt|²`.

The Lipschitz premise is explicit. No pointwise regularity is inferred from membership
in the recording-window `L²` signal space.
-/

namespace IPNPCNS.Signal

noncomputable section

def membraneKernel (Δt τ s : ℝ) : ℝ :=
  τ⁻¹ * Real.exp (-(Δt - s) / τ)

def membraneDecayProfile (Δt τ s : ℝ) : ℝ :=
  Real.exp (-(Δt - s) / τ)

lemma hasDerivAt_membraneDecayProfile (Δt τ s : ℝ) :
    HasDerivAt (membraneDecayProfile Δt τ) (membraneKernel Δt τ s) s := by
  have hinner : HasDerivAt (fun u : ℝ => -(Δt - u) / τ) τ⁻¹ s := by
    convert ((((hasDerivAt_const s Δt).sub (hasDerivAt_id s)).neg).div_const τ) using 1
    all_goals first | rfl | simp [div_eq_mul_inv]
  unfold membraneDecayProfile membraneKernel
  simpa only [mul_comm] using hinner.exp

lemma membraneKernel_intervalIntegrable (Δt τ : ℝ) :
    IntervalIntegrable (membraneKernel Δt τ) volume 0 Δt := by
  apply Continuous.intervalIntegrable
  unfold membraneKernel
  fun_prop

lemma integral_membraneKernel (Δt τ : ℝ) :
    ∫ s in (0 : ℝ)..Δt, membraneKernel Δt τ s =
      membraneUpdateFactor Δt τ := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _hs => hasDerivAt_membraneDecayProfile Δt τ s)
    (membraneKernel_intervalIntegrable Δt τ)]
  simp [membraneDecayProfile, membraneUpdateFactor]

lemma continuous_membraneKernel (Δt τ : ℝ) : Continuous (membraneKernel Δt τ) := by
  unfold membraneKernel
  fun_prop

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

/-- Exact variation-of-constants step for a first-order membrane low-pass response. -/
def exactMembraneStep (Δt τ : ℝ) (drive : ℝ → S) (state : S) : S :=
  membraneDecayProfile Δt τ 0 • state +
    ∫ s in (0 : ℝ)..Δt, membraneKernel Δt τ s • drive s

/-- Error caused by freezing the drive at the beginning of the step. -/
def membraneRemainderValue (Δt τ : ℝ) (drive : ℝ → S) : S :=
  ∫ s in (0 : ℝ)..Δt,
    membraneKernel Δt τ s • (drive s - drive 0)

omit [CompleteSpace S] in
private lemma intervalIntegrable_kernel_smul
    {Δt τ : ℝ} {drive : ℝ → S} (hΔt : 0 ≤ Δt)
    (hdrive : ContinuousOn drive (Set.Icc 0 Δt)) :
    IntervalIntegrable (fun s => membraneKernel Δt τ s • drive s) volume 0 Δt := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hΔt]
  exact (continuous_membraneKernel Δt τ).continuousOn.smul hdrive

omit [CompleteSpace S] in
private lemma intervalIntegrable_kernel_smul_sub
    {Δt τ : ℝ} {drive : ℝ → S} (hΔt : 0 ≤ Δt)
    (hdrive : ContinuousOn drive (Set.Icc 0 Δt)) :
    IntervalIntegrable
      (fun s => membraneKernel Δt τ s • (drive s - drive 0)) volume 0 Δt := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hΔt]
  exact (continuous_membraneKernel Δt τ).continuousOn.smul
    (hdrive.sub continuousOn_const)

theorem exactMembraneStep_eq_firstOrder_add_remainder
    {Δt τ : ℝ} (hΔt : 0 ≤ Δt) {drive : ℝ → S}
    (hdrive : ContinuousOn drive (Set.Icc 0 Δt)) (state : S) :
    exactMembraneStep Δt τ drive state =
      firstOrderMembraneUpdate (membraneUpdateFactor Δt τ) (drive 0) 0 state +
        membraneRemainderValue Δt τ drive := by
  have hconst : IntervalIntegrable
      (fun s => membraneKernel Δt τ s • drive 0) volume 0 Δt :=
    (continuous_membraneKernel Δt τ).smul continuous_const |>.intervalIntegrable 0 Δt
  have hrem := intervalIntegrable_kernel_smul_sub
    (S := S) (τ := τ) hΔt hdrive
  have hsplit :
      (∫ s in (0 : ℝ)..Δt, membraneKernel Δt τ s • drive s) =
        (∫ s in (0 : ℝ)..Δt, membraneKernel Δt τ s • drive 0) +
          ∫ s in (0 : ℝ)..Δt,
            membraneKernel Δt τ s • (drive s - drive 0) := by
    rw [← intervalIntegral.integral_add hconst hrem]
    apply intervalIntegral.integral_congr
    intro s _hs
    change membraneKernel Δt τ s • drive s =
      membraneKernel Δt τ s • drive 0 +
        membraneKernel Δt τ s • (drive s - drive 0)
    rw [← smul_add]
    congr 1
    abel
  rw [exactMembraneStep, hsplit, intervalIntegral.integral_smul_const,
    integral_membraneKernel]
  simp [firstOrderMembraneUpdate, membraneRemainderValue,
    membraneUpdateFactor, membraneDecayProfile]
  abel

/-- A drive that is constant during the step gives the frozen-input update exactly. -/
theorem exactMembraneStep_const {Δt τ : ℝ} (hΔt : 0 ≤ Δt)
    (drive state : S) :
    exactMembraneStep Δt τ (fun _ => drive) state =
      firstOrderMembraneUpdate (membraneUpdateFactor Δt τ) drive 0 state := by
  simpa [membraneRemainderValue] using
    exactMembraneStep_eq_firstOrder_add_remainder
      (S := S) (τ := τ) hΔt continuousOn_const state

lemma membraneKernel_nonneg {Δt τ s : ℝ} (hτ : 0 < τ) :
    0 ≤ membraneKernel Δt τ s := by
  exact mul_nonneg (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le

lemma membraneKernel_le_inv {Δt τ s : ℝ} (hτ : 0 < τ) (hs : s ≤ Δt) :
    membraneKernel Δt τ s ≤ τ⁻¹ := by
  have hexp : Real.exp (-(Δt - s) / τ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sub_nonneg.mpr hs)) hτ.le
  simpa [membraneKernel] using
    mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr hτ.le)

omit [CompleteSpace S] in
theorem norm_membraneRemainderValue_le
    {Δt τ : ℝ} (hΔt : 0 ≤ Δt) (hτ : 0 < τ)
    {L : ℝ≥0} {drive : ℝ → S}
    (hdrive : LipschitzOnWith L drive (Set.Icc 0 Δt)) :
    ‖membraneRemainderValue Δt τ drive‖ ≤
      ((L : ℝ) / τ) * |Δt| ^ 2 := by
  unfold membraneRemainderValue
  calc
    ‖∫ s in (0 : ℝ)..Δt,
        membraneKernel Δt τ s • (drive s - drive 0)‖ ≤
        (((L : ℝ) / τ) * Δt) * |Δt - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [Set.uIoc_of_le hΔt] at hs
      have hdriveBound : ‖drive s - drive 0‖ ≤ (L : ℝ) * |s| := by
        simpa only [Real.norm_eq_abs, sub_zero] using
          hdrive.norm_sub_le ⟨hs.1.le, hs.2⟩ ⟨le_rfl, hΔt⟩
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (membraneKernel_nonneg hτ)]
      calc
        membraneKernel Δt τ s * ‖drive s - drive 0‖ ≤
            τ⁻¹ * ((L : ℝ) * |s|) := by
          exact mul_le_mul (membraneKernel_le_inv hτ hs.2) hdriveBound
            (norm_nonneg _) (inv_nonneg.mpr hτ.le)
        _ ≤ τ⁻¹ * ((L : ℝ) * Δt) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hτ.le)
          apply mul_le_mul_of_nonneg_left _ NNReal.zero_le_coe
          simpa [abs_of_nonneg hs.1.le] using hs.2
        _ = ((L : ℝ) / τ) * Δt := by
          rw [div_eq_mul_inv]
          ring
    _ = ((L : ℝ) / τ) * |Δt| ^ 2 := by
      rw [sub_zero, abs_of_nonneg hΔt]
      ring

/-- The varying-drive integral gives a concrete witness for equation (33)'s
quadratic remainder. -/
def membraneQuadraticRemainder
    {Δt τ : ℝ} (hΔt : 0 ≤ Δt) (hτ : 0 < τ)
    {L : ℝ≥0} {drive : ℝ → S}
    (hdrive : LipschitzOnWith L drive (Set.Icc 0 Δt)) :
    QuadraticRemainder (S := S) Δt where
  value := membraneRemainderValue Δt τ drive
  constant := (L : ℝ) / τ
  constant_nonnegative := div_nonneg NNReal.zero_le_coe hτ.le
  norm_le := norm_membraneRemainderValue_le hΔt hτ hdrive

theorem exactMembraneStep_eq_updateWithRemainder
    {Δt τ : ℝ} (hΔt : 0 ≤ Δt) (hτ : 0 < τ)
    {L : ℝ≥0} {drive : ℝ → S}
    (hdrive : LipschitzOnWith L drive (Set.Icc 0 Δt)) (state : S) :
    exactMembraneStep Δt τ drive state =
      membraneUpdateWithRemainder (membraneUpdateFactor Δt τ)
        (drive 0) 0 state (membraneQuadraticRemainder hΔt hτ hdrive) := by
  rw [exactMembraneStep_eq_firstOrder_add_remainder hΔt hdrive.continuousOn]
  rfl

/-- Net feedforward drive in equation (33). -/
def membraneNetDrive (excitation inhibition : ℝ → S) (s : ℝ) : S :=
  excitation s - inhibition s

/-- Exact membrane step with separate excitatory and inhibitory drives. -/
def exactMembraneUpdate (Δt τ : ℝ) (excitation inhibition : ℝ → S)
    (state : S) : S :=
  exactMembraneStep Δt τ (membraneNetDrive excitation inhibition) state

/-- Concrete quadratic remainder for the separate excitation/inhibition spelling of
equation (33). -/
def membraneNetQuadraticRemainder
    {Δt τ : ℝ} (hΔt : 0 ≤ Δt) (hτ : 0 < τ)
    {L : ℝ≥0} {excitation inhibition : ℝ → S}
    (hdrive : LipschitzOnWith L (membraneNetDrive excitation inhibition)
      (Set.Icc 0 Δt)) :
    QuadraticRemainder (S := S) Δt :=
  membraneQuadraticRemainder hΔt hτ hdrive

/-- Equation (33) with its `O(Δt²)` term derived from a Lipschitz net drive. -/
theorem exactMembraneUpdate_eq_updateWithRemainder
    {Δt τ : ℝ} (hΔt : 0 ≤ Δt) (hτ : 0 < τ)
    {L : ℝ≥0} {excitation inhibition : ℝ → S}
    (hdrive : LipschitzOnWith L (membraneNetDrive excitation inhibition)
      (Set.Icc 0 Δt)) (state : S) :
    exactMembraneUpdate Δt τ excitation inhibition state =
      membraneUpdateWithRemainder (membraneUpdateFactor Δt τ)
        (excitation 0) (inhibition 0) state
        (membraneNetQuadraticRemainder hΔt hτ hdrive) := by
  rw [exactMembraneUpdate, exactMembraneStep_eq_firstOrder_add_remainder
    hΔt hdrive.continuousOn]
  simp [membraneUpdateWithRemainder, firstOrderMembraneUpdate,
    membraneNetDrive, membraneNetQuadraticRemainder,
    membraneQuadraticRemainder]

end

end IPNPCNS.Signal
