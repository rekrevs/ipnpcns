import IPNPCNS.Signal.Deterministic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The paper's orthonormal wavelet example

This file formalizes the three finite-duration wavelets used in Section 3.2 of
the paper.  The recording window is exactly `T = 0.20 s`, the envelope is
`sin²(πt/T)` on `[0,T]` and zero elsewhere, and the carrier frequencies are
30, 30, and 60 Hz.  With the paper's normalization `4 / √(3T)`, the three
signals have zero mean and form an orthonormal family in the recording-window
`L²` space.

The final section verifies the three least-squares examples from the paper.
It also makes the baseline-subtraction convention explicit: literal firing
rates may include a constant baseline, but every `L²` target and inner product
in the examples uses the baseline-subtracted modulation.
-/

open MeasureTheory Set
open scoped ENNReal MeasureTheory Interval

namespace IPNPCNS
namespace WaveletExample

noncomputable section

/-- The example's exact recording duration: `0.20 s`. -/
def recordingWindow : ℝ := 1 / 5

/-- The rational recording duration is exactly the decimal value used in the
paper. -/
theorem recordingWindow_eq : recordingWindow = (0.20 : ℝ) := by
  norm_num [recordingWindow]

private def cosMode (k : ℕ) (t : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * (k : ℝ) * t / recordingWindow)

private def sinMode (k : ℕ) (t : ℝ) : ℝ :=
  Real.sin (2 * Real.pi * (k : ℝ) * t / recordingWindow)

@[fun_prop]
private lemma cosMode_continuous (k : ℕ) : Continuous (cosMode k) := by
  unfold cosMode
  fun_prop

@[fun_prop]
private lemma sinMode_continuous (k : ℕ) : Continuous (sinMode k) := by
  unfold sinMode
  fun_prop

private lemma cos_mode_integral {k : ℕ} (hk : k ≠ 0) :
    (∫ t in (0 : ℝ)..recordingWindow, cosMode k t) = 0 := by
  let c : ℝ := 2 * Real.pi * (k : ℝ) / recordingWindow
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hk)
  have hc : c ≠ 0 := by
    dsimp [c, recordingWindow]
    positivity
  have hend : c * recordingWindow = (k : ℝ) * (2 * Real.pi) := by
    dsimp [c, recordingWindow]
    ring
  have hfun : cosMode k = fun t => Real.cos (c * t) := by
    funext t
    apply congrArg Real.cos
    simp only [c]
    ring
  rw [hfun]
  rw [intervalIntegral.integral_comp_mul_left Real.cos hc, hend]
  have hsin : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
    rw [show (k : ℝ) * (2 * Real.pi) = ((2 * k : ℕ) : ℝ) * Real.pi by
      push_cast
      ring]
    exact Real.sin_nat_mul_pi (2 * k)
  simp [integral_cos, hsin]

private lemma sin_mode_integral {k : ℕ} (hk : k ≠ 0) :
    (∫ t in (0 : ℝ)..recordingWindow, sinMode k t) = 0 := by
  let c : ℝ := 2 * Real.pi * (k : ℝ) / recordingWindow
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hk)
  have hc : c ≠ 0 := by
    dsimp [c, recordingWindow]
    positivity
  have hend : c * recordingWindow = (k : ℝ) * (2 * Real.pi) := by
    dsimp [c, recordingWindow]
    ring
  have hfun : sinMode k = fun t => Real.sin (c * t) := by
    funext t
    apply congrArg Real.sin
    simp only [c]
    ring
  rw [hfun]
  rw [intervalIntegral.integral_comp_mul_left Real.sin hc, hend]
  simp [integral_sin, Real.cos_nat_mul_two_pi]

private lemma sin_mode_integral_all (k : ℕ) :
    (∫ t in (0 : ℝ)..recordingWindow, sinMode k t) = 0 := by
  by_cases hk : k = 0
  · subst k
    simp [sinMode]
  · exact sin_mode_integral hk

private lemma cos_mode_add_integral {m k : ℕ} (hm : m ≠ 0) (hk : k ≠ 0) :
    (∫ t in (0 : ℝ)..recordingWindow, cosMode m t + cosMode k t) = 0 := by
  rw [intervalIntegral.integral_add
    ((cosMode_continuous m).intervalIntegrable 0 recordingWindow)
    ((cosMode_continuous k).intervalIntegrable 0 recordingWindow),
    cos_mode_integral hm, cos_mode_integral hk, add_zero]

private lemma sin_mode_add_integral (m k : ℕ) :
    (∫ t in (0 : ℝ)..recordingWindow, sinMode m t + sinMode k t) = 0 := by
  rw [intervalIntegral.integral_add
    ((sinMode_continuous m).intervalIntegrable 0 recordingWindow)
    ((sinMode_continuous k).intervalIntegrable 0 recordingWindow),
    sin_mode_integral_all, sin_mode_integral_all, add_zero]

private lemma cos_mode_mul_cos_mode_of_le {m k : ℕ} (hmk : m ≤ k) (t : ℝ) :
    cosMode m t * cosMode k t =
      (cosMode (m + k) t + cosMode (k - m) t) / 2 := by
  have hplus :
      2 * Real.pi * ((m + k : ℕ) : ℝ) * t / recordingWindow =
        2 * Real.pi * (m : ℝ) * t / recordingWindow +
          2 * Real.pi * (k : ℝ) * t / recordingWindow := by
    push_cast
    ring
  have hminus :
      2 * Real.pi * ((k - m : ℕ) : ℝ) * t / recordingWindow =
        2 * Real.pi * (k : ℝ) * t / recordingWindow -
          2 * Real.pi * (m : ℝ) * t / recordingWindow := by
    rw [Nat.cast_sub hmk]
    ring
  rw [cosMode, cosMode, cosMode, cosMode, hplus, hminus,
    Real.cos_add, Real.cos_sub]
  ring

private lemma cos_mode_mul_sin_mode_of_le {m k : ℕ} (hmk : m ≤ k) (t : ℝ) :
    cosMode m t * sinMode k t =
      (sinMode (m + k) t + sinMode (k - m) t) / 2 := by
  have hplus :
      2 * Real.pi * ((m + k : ℕ) : ℝ) * t / recordingWindow =
        2 * Real.pi * (m : ℝ) * t / recordingWindow +
          2 * Real.pi * (k : ℝ) * t / recordingWindow := by
    push_cast
    ring
  have hminus :
      2 * Real.pi * ((k - m : ℕ) : ℝ) * t / recordingWindow =
        2 * Real.pi * (k : ℝ) * t / recordingWindow -
          2 * Real.pi * (m : ℝ) * t / recordingWindow := by
    rw [Nat.cast_sub hmk]
    ring
  rw [cosMode, sinMode, sinMode, sinMode, hplus, hminus,
    Real.sin_add, Real.sin_sub]
  ring

private lemma sin_mode_mul_cos_mode_of_le {m k : ℕ} (hmk : m ≤ k) (t : ℝ) :
    sinMode m t * cosMode k t =
      (sinMode (m + k) t - sinMode (k - m) t) / 2 := by
  have hplus :
      2 * Real.pi * ((m + k : ℕ) : ℝ) * t / recordingWindow =
        2 * Real.pi * (m : ℝ) * t / recordingWindow +
          2 * Real.pi * (k : ℝ) * t / recordingWindow := by
    push_cast
    ring
  have hminus :
      2 * Real.pi * ((k - m : ℕ) : ℝ) * t / recordingWindow =
        2 * Real.pi * (k : ℝ) * t / recordingWindow -
          2 * Real.pi * (m : ℝ) * t / recordingWindow := by
    rw [Nat.cast_sub hmk]
    ring
  rw [sinMode, cosMode, sinMode, sinMode, hplus, hminus,
    Real.sin_add, Real.sin_sub]
  ring

private lemma cos_mode_sq (k : ℕ) (t : ℝ) :
    cosMode k t ^ 2 = (1 + cosMode (2 * k) t) / 2 := by
  have hdouble :
      2 * Real.pi * (((2 * k : ℕ) : ℝ)) * t / recordingWindow =
        2 * (2 * Real.pi * (k : ℝ) * t / recordingWindow) := by
    push_cast
    ring
  rw [cosMode, cosMode, hdouble, Real.cos_two_mul]
  ring

private lemma sin_mode_sq (k : ℕ) (t : ℝ) :
    sinMode k t ^ 2 = (1 - cosMode (2 * k) t) / 2 := by
  let x := 2 * Real.pi * (k : ℝ) * t / recordingWindow
  have htrig := Real.sin_sq_add_cos_sq x
  have hcos : Real.cos x ^ 2 = (1 + cosMode (2 * k) t) / 2 := by
    simpa only [cosMode, x] using cos_mode_sq k t
  change Real.sin x ^ 2 = (1 - cosMode (2 * k) t) / 2
  linarith

private def hannCore (t : ℝ) : ℝ :=
  Real.sin (Real.pi * t / recordingWindow) ^ 2

private lemma hann_core_eq (t : ℝ) :
    hannCore t = (1 - cosMode 1 t) / 2 := by
  let x := Real.pi * t / recordingWindow
  have htrig := Real.sin_sq_add_cos_sq x
  have hdouble := Real.cos_two_mul x
  have hmode : cosMode 1 t = Real.cos (2 * x) := by
    apply congrArg Real.cos
    simp only [x, Nat.cast_one]
    ring
  change Real.sin x ^ 2 = (1 - cosMode 1 t) / 2
  rw [hmode]
  nlinarith

private lemma hann_core_sq_eq (t : ℝ) :
    hannCore t ^ 2 =
      3 / 8 - (1 / 2) * cosMode 1 t + (1 / 8) * cosMode 2 t := by
  rw [hann_core_eq]
  have hsquare := cos_mode_sq 1 t
  norm_num at hsquare ⊢
  nlinarith

private lemma hann_core_sq_integral :
    (∫ t in (0 : ℝ)..recordingWindow, hannCore t ^ 2) =
      3 * recordingWindow / 8 := by
  calc
    (∫ t in (0 : ℝ)..recordingWindow, hannCore t ^ 2) =
        ∫ t in (0 : ℝ)..recordingWindow,
          (3 / 8 : ℝ) - (1 / 2) * cosMode 1 t +
            (1 / 8) * cosMode 2 t := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      exact hann_core_sq_eq t
    _ = 3 * recordingWindow / 8 := by
      rw [intervalIntegral.integral_add
          ((show Continuous (fun t => (3 / 8 : ℝ) - (1 / 2) * cosMode 1 t) by
            fun_prop).intervalIntegrable 0 recordingWindow)
          ((show Continuous (fun t => (1 / 8 : ℝ) * cosMode 2 t) by
            fun_prop).intervalIntegrable 0 recordingWindow),
        intervalIntegral.integral_sub
          ((show Continuous (fun _t : ℝ => (3 / 8 : ℝ)) by
            fun_prop).intervalIntegrable 0 recordingWindow)
          ((show Continuous (fun t => (1 / 2 : ℝ) * cosMode 1 t) by
            fun_prop).intervalIntegrable 0 recordingWindow)]
      simp_rw [intervalIntegral.integral_const_mul]
      rw [cos_mode_integral (k := 1) (by norm_num),
        cos_mode_integral (k := 2) (by norm_num)]
      norm_num [recordingWindow]

private lemma hann_core_mul_cos_mode_integral {k : ℕ} (hk : 2 ≤ k) :
    (∫ t in (0 : ℝ)..recordingWindow, hannCore t * cosMode k t) = 0 := by
  have h1 : 1 ≤ k := le_trans (by norm_num) hk
  have hk0 : k ≠ 0 := by omega
  have hkm10 : k - 1 ≠ 0 := by omega
  have hkp10 : k + 1 ≠ 0 := by omega
  calc
    (∫ t in (0 : ℝ)..recordingWindow, hannCore t * cosMode k t) =
        ∫ t in (0 : ℝ)..recordingWindow,
          (1 / 2 : ℝ) * cosMode k t -
            (1 / 4) * (cosMode (1 + k) t + cosMode (k - 1) t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      rw [hann_core_eq]
      have hproduct := cos_mode_mul_cos_mode_of_le h1 t
      nlinarith
    _ = 0 := by
      rw [intervalIntegral.integral_sub
        ((show Continuous (fun t => (1 / 2 : ℝ) * cosMode k t) by
          fun_prop).intervalIntegrable 0 recordingWindow)
        ((show Continuous (fun t =>
          (1 / 4 : ℝ) * (cosMode (1 + k) t + cosMode (k - 1) t)) by
            fun_prop).intervalIntegrable 0 recordingWindow)]
      simp_rw [intervalIntegral.integral_const_mul]
      rw [cos_mode_integral hk0,
        cos_mode_add_integral (by omega) hkm10]
      ring

private lemma hann_core_mul_sin_mode_integral {k : ℕ} (hk : 1 ≤ k) :
    (∫ t in (0 : ℝ)..recordingWindow, hannCore t * sinMode k t) = 0 := by
  calc
    (∫ t in (0 : ℝ)..recordingWindow, hannCore t * sinMode k t) =
        ∫ t in (0 : ℝ)..recordingWindow,
          (1 / 2 : ℝ) * sinMode k t -
            (1 / 4) * (sinMode (1 + k) t + sinMode (k - 1) t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      rw [hann_core_eq]
      have hproduct := cos_mode_mul_sin_mode_of_le hk t
      nlinarith
    _ = 0 := by
      rw [intervalIntegral.integral_sub
        ((show Continuous (fun t => (1 / 2 : ℝ) * sinMode k t) by
          fun_prop).intervalIntegrable 0 recordingWindow)
        ((show Continuous (fun t =>
          (1 / 4 : ℝ) * (sinMode (1 + k) t + sinMode (k - 1) t)) by
            fun_prop).intervalIntegrable 0 recordingWindow)]
      simp_rw [intervalIntegral.integral_const_mul]
      rw [sin_mode_integral_all,
        sin_mode_add_integral]
      ring

private lemma hann_core_sq_mul_cos_mode_integral {k : ℕ} (hk : 3 ≤ k) :
    (∫ t in (0 : ℝ)..recordingWindow, hannCore t ^ 2 * cosMode k t) = 0 := by
  have h1 : 1 ≤ k := by omega
  have h2 : 2 ≤ k := by omega
  have hk0 : k ≠ 0 := by omega
  have hkp10 : 1 + k ≠ 0 := by omega
  have hkm10 : k - 1 ≠ 0 := by omega
  have hkp20 : 2 + k ≠ 0 := by omega
  have hkm20 : k - 2 ≠ 0 := by omega
  calc
    (∫ t in (0 : ℝ)..recordingWindow, hannCore t ^ 2 * cosMode k t) =
        ∫ t in (0 : ℝ)..recordingWindow,
          (3 / 8 : ℝ) * cosMode k t -
            (1 / 4) * (cosMode (1 + k) t + cosMode (k - 1) t) +
            (1 / 16) * (cosMode (2 + k) t + cosMode (k - 2) t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      rw [hann_core_sq_eq]
      have hproduct1 := cos_mode_mul_cos_mode_of_le h1 t
      have hproduct2 := cos_mode_mul_cos_mode_of_le h2 t
      nlinarith
    _ = 0 := by
      rw [intervalIntegral.integral_add
          ((show Continuous (fun t =>
            (3 / 8 : ℝ) * cosMode k t -
              (1 / 4) * (cosMode (1 + k) t + cosMode (k - 1) t)) by
                fun_prop).intervalIntegrable 0 recordingWindow)
          ((show Continuous (fun t =>
            (1 / 16 : ℝ) * (cosMode (2 + k) t + cosMode (k - 2) t)) by
              fun_prop).intervalIntegrable 0 recordingWindow),
        intervalIntegral.integral_sub
          ((show Continuous (fun t => (3 / 8 : ℝ) * cosMode k t) by
            fun_prop).intervalIntegrable 0 recordingWindow)
          ((show Continuous (fun t =>
            (1 / 4 : ℝ) * (cosMode (1 + k) t + cosMode (k - 1) t)) by
              fun_prop).intervalIntegrable 0 recordingWindow)]
      simp_rw [intervalIntegral.integral_const_mul]
      rw [cos_mode_integral hk0,
        cos_mode_add_integral hkp10 hkm10,
        cos_mode_add_integral hkp20 hkm20]
      ring

private lemma hann_core_sq_mul_sin_mode_integral {k : ℕ} (hk : 2 ≤ k) :
    (∫ t in (0 : ℝ)..recordingWindow, hannCore t ^ 2 * sinMode k t) = 0 := by
  have h1 : 1 ≤ k := by omega
  calc
    (∫ t in (0 : ℝ)..recordingWindow, hannCore t ^ 2 * sinMode k t) =
        ∫ t in (0 : ℝ)..recordingWindow,
          (3 / 8 : ℝ) * sinMode k t -
            (1 / 4) * (sinMode (1 + k) t + sinMode (k - 1) t) +
            (1 / 16) * (sinMode (2 + k) t + sinMode (k - 2) t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      rw [hann_core_sq_eq]
      have hproduct1 := cos_mode_mul_sin_mode_of_le h1 t
      have hproduct2 := cos_mode_mul_sin_mode_of_le hk t
      nlinarith
    _ = 0 := by
      rw [intervalIntegral.integral_add
          ((show Continuous (fun t =>
            (3 / 8 : ℝ) * sinMode k t -
              (1 / 4) * (sinMode (1 + k) t + sinMode (k - 1) t)) by
                fun_prop).intervalIntegrable 0 recordingWindow)
          ((show Continuous (fun t =>
            (1 / 16 : ℝ) * (sinMode (2 + k) t + sinMode (k - 2) t)) by
              fun_prop).intervalIntegrable 0 recordingWindow),
        intervalIntegral.integral_sub
          ((show Continuous (fun t => (3 / 8 : ℝ) * sinMode k t) by
            fun_prop).intervalIntegrable 0 recordingWindow)
          ((show Continuous (fun t =>
            (1 / 4 : ℝ) * (sinMode (1 + k) t + sinMode (k - 1) t)) by
              fun_prop).intervalIntegrable 0 recordingWindow)]
      simp_rw [intervalIntegral.integral_const_mul]
      rw [sin_mode_integral_all,
        sin_mode_add_integral,
        sin_mode_add_integral]
      ring

private lemma hann_core_mul_cos_mode_sq_integral {k : ℕ} (hk : 2 ≤ k) :
    (∫ t in (0 : ℝ)..recordingWindow,
      (hannCore t * cosMode k t) ^ 2) = 3 * recordingWindow / 16 := by
  have htwok : 3 ≤ 2 * k := by omega
  calc
    (∫ t in (0 : ℝ)..recordingWindow,
        (hannCore t * cosMode k t) ^ 2) =
      ∫ t in (0 : ℝ)..recordingWindow,
        (1 / 2 : ℝ) *
          (hannCore t ^ 2 +
            hannCore t ^ 2 * cosMode (2 * k) t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      rw [mul_pow, cos_mode_sq]
      ring
    _ = 3 * recordingWindow / 16 := by
      simp_rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_add
        ((show Continuous (fun t => hannCore t ^ 2) by
          unfold hannCore
          fun_prop).intervalIntegrable 0 recordingWindow)
        ((show Continuous (fun t =>
          hannCore t ^ 2 * cosMode (2 * k) t) by
            unfold hannCore
            fun_prop).intervalIntegrable 0 recordingWindow),
        hann_core_sq_integral,
        hann_core_sq_mul_cos_mode_integral htwok]
      ring

private lemma hann_core_mul_sin_mode_sq_integral {k : ℕ} (hk : 2 ≤ k) :
    (∫ t in (0 : ℝ)..recordingWindow,
      (hannCore t * sinMode k t) ^ 2) = 3 * recordingWindow / 16 := by
  have htwok : 3 ≤ 2 * k := by omega
  calc
    (∫ t in (0 : ℝ)..recordingWindow,
        (hannCore t * sinMode k t) ^ 2) =
      ∫ t in (0 : ℝ)..recordingWindow,
        (1 / 2 : ℝ) *
          (hannCore t ^ 2 -
            hannCore t ^ 2 * cosMode (2 * k) t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      rw [mul_pow, sin_mode_sq]
      ring
    _ = 3 * recordingWindow / 16 := by
      simp_rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_sub
        ((show Continuous (fun t => hannCore t ^ 2) by
          unfold hannCore
          fun_prop).intervalIntegrable 0 recordingWindow)
        ((show Continuous (fun t =>
          hannCore t ^ 2 * cosMode (2 * k) t) by
            unfold hannCore
            fun_prop).intervalIntegrable 0 recordingWindow),
        hann_core_sq_integral,
        hann_core_sq_mul_cos_mode_integral htwok]
      ring

private lemma first_cos_sin_cross_integral :
    (∫ t in (0 : ℝ)..recordingWindow,
      (hannCore t * cosMode 6 t) *
        (hannCore t * sinMode 6 t)) = 0 := by
  calc
    (∫ t in (0 : ℝ)..recordingWindow,
        (hannCore t * cosMode 6 t) *
          (hannCore t * sinMode 6 t)) =
      ∫ t in (0 : ℝ)..recordingWindow,
        (1 / 2 : ℝ) * hannCore t ^ 2 * sinMode 12 t := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      have hproduct := cos_mode_mul_sin_mode_of_le (m := 6) (k := 6) (by norm_num) t
      have hzero : sinMode 0 t = 0 := by simp [sinMode]
      rw [hzero, add_zero] at hproduct
      calc
        hannCore t * cosMode 6 t * (hannCore t * sinMode 6 t) =
            hannCore t ^ 2 * (cosMode 6 t * sinMode 6 t) := by ring
        _ = (1 / 2 : ℝ) * hannCore t ^ 2 * sinMode 12 t := by
          rw [hproduct]
          ring
    _ = 0 := by
      rw [show (fun t => (1 / 2 : ℝ) * hannCore t ^ 2 * sinMode 12 t) =
          fun t => (1 / 2 : ℝ) * (hannCore t ^ 2 * sinMode 12 t) by
        funext t
        ring,
        intervalIntegral.integral_const_mul,
        hann_core_sq_mul_sin_mode_integral (by norm_num)]
      ring

private lemma first_second_cos_cross_integral :
    (∫ t in (0 : ℝ)..recordingWindow,
      (hannCore t * cosMode 6 t) *
        (hannCore t * cosMode 12 t)) = 0 := by
  calc
    (∫ t in (0 : ℝ)..recordingWindow,
        (hannCore t * cosMode 6 t) *
          (hannCore t * cosMode 12 t)) =
      ∫ t in (0 : ℝ)..recordingWindow,
        (1 / 2 : ℝ) *
          (hannCore t ^ 2 * cosMode 18 t +
            hannCore t ^ 2 * cosMode 6 t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      have hproduct := cos_mode_mul_cos_mode_of_le
        (m := 6) (k := 12) (by norm_num) t
      norm_num at hproduct
      nlinarith
    _ = 0 := by
      simp_rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_add
        ((show Continuous (fun t =>
          hannCore t ^ 2 * cosMode 18 t) by
            unfold hannCore
            fun_prop).intervalIntegrable 0 recordingWindow)
        ((show Continuous (fun t =>
          hannCore t ^ 2 * cosMode 6 t) by
            unfold hannCore
            fun_prop).intervalIntegrable 0 recordingWindow),
        hann_core_sq_mul_cos_mode_integral (by norm_num),
        hann_core_sq_mul_cos_mode_integral (by norm_num)]
      ring

private lemma first_sin_second_cos_cross_integral :
    (∫ t in (0 : ℝ)..recordingWindow,
      (hannCore t * sinMode 6 t) *
        (hannCore t * cosMode 12 t)) = 0 := by
  calc
    (∫ t in (0 : ℝ)..recordingWindow,
        (hannCore t * sinMode 6 t) *
          (hannCore t * cosMode 12 t)) =
      ∫ t in (0 : ℝ)..recordingWindow,
        (1 / 2 : ℝ) *
          (hannCore t ^ 2 * sinMode 18 t -
            hannCore t ^ 2 * sinMode 6 t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only
      have hproduct := sin_mode_mul_cos_mode_of_le
        (m := 6) (k := 12) (by norm_num) t
      norm_num at hproduct
      nlinarith
    _ = 0 := by
      simp_rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_sub
        ((show Continuous (fun t =>
          hannCore t ^ 2 * sinMode 18 t) by
            unfold hannCore
            fun_prop).intervalIntegrable 0 recordingWindow)
        ((show Continuous (fun t =>
          hannCore t ^ 2 * sinMode 6 t) by
            unfold hannCore
            fun_prop).intervalIntegrable 0 recordingWindow),
        hann_core_sq_mul_sin_mode_integral (by norm_num),
        hann_core_sq_mul_sin_mode_integral (by norm_num)]
      ring

/-- The paper's common wavelet normalization, `γ = 4 / √(3T)`. -/
def normalization : ℝ := 4 / √(3 * recordingWindow)

/-- The zero-extended `sin²(πt/T)` envelope on the recording window. -/
def hannEnvelope (t : ℝ) : ℝ :=
  if t ∈ Set.Icc (0 : ℝ) recordingWindow then hannCore t else 0

/-- Names for the paper's cosine-30-Hz, sine-30-Hz, and cosine-60-Hz
wavelets. -/
inductive WaveletIndex where
  | cosine30
  | sine30
  | cosine60
  deriving DecidableEq, Fintype

/-- The carrier associated with each of the three paper wavelets. -/
def carrier : WaveletIndex → ℝ → ℝ
  | .cosine30 => cosMode 6
  | .sine30 => sinMode 6
  | .cosine60 => cosMode 12

/-- A measurable pointwise representative of a normalized paper wavelet. -/
def waveletRepresentative (i : WaveletIndex) (t : ℝ) : ℝ :=
  normalization * hannEnvelope t * carrier i t

/-- On its support, the envelope has exactly the formula displayed in the
paper. -/
theorem hannEnvelope_of_mem {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) recordingWindow) :
    hannEnvelope t = Real.sin (Real.pi * t / recordingWindow) ^ 2 := by
  simp [hannEnvelope, hannCore, ht]

/-- Off the recording window, the envelope is zero. -/
theorem hannEnvelope_of_not_mem {t : ℝ}
    (ht : t ∉ Set.Icc (0 : ℝ) recordingWindow) :
    hannEnvelope t = 0 := by
  simp [hannEnvelope, ht]

@[simp]
theorem carrier_cosine30 (t : ℝ) :
    carrier .cosine30 t = Real.cos (2 * Real.pi * 30 * t) := by
  simp only [carrier, cosMode, recordingWindow]
  congr 1
  ring

@[simp]
theorem carrier_sine30 (t : ℝ) :
    carrier .sine30 t = Real.sin (2 * Real.pi * 30 * t) := by
  simp only [carrier, sinMode, recordingWindow]
  congr 1
  ring

@[simp]
theorem carrier_cosine60 (t : ℝ) :
    carrier .cosine60 t = Real.cos (2 * Real.pi * 60 * t) := by
  simp only [carrier, cosMode, recordingWindow]
  congr 1
  ring

private lemma hannCore_continuous : Continuous hannCore := by
  unfold hannCore
  fun_prop

private lemma hannEnvelope_measurable : Measurable hannEnvelope := by
  unfold hannEnvelope
  exact Measurable.ite measurableSet_Icc hannCore_continuous.measurable measurable_const

private lemma carrier_continuous (i : WaveletIndex) : Continuous (carrier i) := by
  cases i <;> simp only [carrier] <;> fun_prop

private lemma waveletRepresentative_measurable (i : WaveletIndex) :
    Measurable (waveletRepresentative i) := by
  unfold waveletRepresentative
  exact (measurable_const.mul hannEnvelope_measurable).mul
    (carrier_continuous i).measurable

private lemma hannEnvelope_abs_le_one (t : ℝ) : |hannEnvelope t| ≤ 1 := by
  unfold hannEnvelope
  split_ifs
  · rw [abs_of_nonneg (sq_nonneg _)]
    exact Real.sin_sq_le_one _
  · simp

private lemma carrier_abs_le_one (i : WaveletIndex) (t : ℝ) :
    |carrier i t| ≤ 1 := by
  cases i
  · exact Real.abs_cos_le_one _
  · exact Real.abs_sin_le_one _
  · exact Real.abs_cos_le_one _

private lemma waveletRepresentative_abs_le (i : WaveletIndex) (t : ℝ) :
    |waveletRepresentative i t| ≤ |normalization| := by
  rw [waveletRepresentative, abs_mul, abs_mul]
  have hGamma : 0 ≤ |normalization| := abs_nonneg _
  calc
    |normalization| * |hannEnvelope t| * |carrier i t| ≤
        |normalization| * 1 * |carrier i t| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hannEnvelope_abs_le_one t) hGamma)
        (abs_nonneg _)
    _ ≤ |normalization| * 1 * 1 := by
      exact mul_le_mul_of_nonneg_left (carrier_abs_le_one i t)
        (mul_nonneg hGamma zero_le_one)
    _ = |normalization| := by ring

private lemma waveletRepresentative_memLp (i : WaveletIndex) :
    MemLp (waveletRepresentative i) 2
      (IPNPCNS.Signal.recordingMeasure recordingWindow) := by
  letI : IsFiniteMeasure (IPNPCNS.Signal.recordingMeasure recordingWindow) :=
    ⟨by simp⟩
  apply MemLp.of_bound
    (waveletRepresentative_measurable i).aestronglyMeasurable |normalization|
  exact Filter.Eventually.of_forall fun t => by
    simpa only [Real.norm_eq_abs] using waveletRepresentative_abs_le i t

/-- The `L²` equivalence class represented by a paper wavelet. -/
def wavelet (i : WaveletIndex) : IPNPCNS.Signal.ScalarSignal recordingWindow :=
  (waveletRepresentative_memLp i).toLp (waveletRepresentative i)

/-- The `L²` wavelet agrees almost everywhere with its displayed formula. -/
theorem wavelet_apply_ae (i : WaveletIndex) :
    wavelet i =ᵐ[IPNPCNS.Signal.recordingMeasure recordingWindow]
      waveletRepresentative i :=
  (waveletRepresentative_memLp i).coeFn_toLp

/-- Integral of a scalar signal over the paper's recording window. -/
def signalIntegral (x : IPNPCNS.Signal.ScalarSignal recordingWindow) : ℝ :=
  ∫ t, x t ∂IPNPCNS.Signal.recordingMeasure recordingWindow

private lemma signalIntegral_wavelet_eq (i : WaveletIndex) :
    signalIntegral (wavelet i) =
      ∫ t in Set.Icc (0 : ℝ) recordingWindow, waveletRepresentative i t := by
  unfold signalIntegral IPNPCNS.Signal.recordingMeasure
  exact integral_congr_ae (wavelet_apply_ae i)

private lemma wavelet_inner_eq (i j : WaveletIndex) :
    inner ℝ (wavelet i) (wavelet j) =
      ∫ t in Set.Icc (0 : ℝ) recordingWindow,
        waveletRepresentative i t * waveletRepresentative j t := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [wavelet_apply_ae i, wavelet_apply_ae j] with t hi hj
  change inner ℝ ((wavelet i : ℝ → ℝ) t)
      ((wavelet j : ℝ → ℝ) t) = _
  rw [hi, hj]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private lemma setIntegral_Icc_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ t in Set.Icc (0 : ℝ) recordingWindow, f t) =
      ∫ t in (0 : ℝ)..recordingWindow, f t := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le]
  norm_num [recordingWindow]

private lemma hannEnvelope_eq_core {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) recordingWindow) :
    hannEnvelope t = hannCore t := by
  simp [hannEnvelope, ht]

private def coreWavelet (i : WaveletIndex) (t : ℝ) : ℝ :=
  hannCore t * carrier i t

private lemma waveletRepresentative_eq_on_window (i : WaveletIndex)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) recordingWindow) :
    waveletRepresentative i t = normalization * coreWavelet i t := by
  simp only [waveletRepresentative, coreWavelet,
    hannEnvelope_eq_core ht]
  ring

private lemma coreWavelet_integral_zero (i : WaveletIndex) :
    (∫ t in (0 : ℝ)..recordingWindow, coreWavelet i t) = 0 := by
  cases i
  · exact hann_core_mul_cos_mode_integral (by norm_num)
  · exact hann_core_mul_sin_mode_integral (by norm_num)
  · exact hann_core_mul_cos_mode_integral (by norm_num)

private lemma waveletRepresentative_setIntegral_zero (i : WaveletIndex) :
    (∫ t in Set.Icc (0 : ℝ) recordingWindow,
      waveletRepresentative i t) = 0 := by
  calc
    (∫ t in Set.Icc (0 : ℝ) recordingWindow,
        waveletRepresentative i t) =
        ∫ t in Set.Icc (0 : ℝ) recordingWindow,
          normalization * coreWavelet i t := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact waveletRepresentative_eq_on_window i ht
    _ = ∫ t in (0 : ℝ)..recordingWindow,
          normalization * coreWavelet i t :=
      setIntegral_Icc_eq_intervalIntegral _
    _ = normalization *
          ∫ t in (0 : ℝ)..recordingWindow, coreWavelet i t := by
      rw [intervalIntegral.integral_const_mul]
    _ = 0 := by rw [coreWavelet_integral_zero, mul_zero]

/-- Every paper wavelet has zero temporal mean. -/
theorem wavelet_zero_mean (i : WaveletIndex) :
    signalIntegral (wavelet i) = 0 := by
  rw [signalIntegral_wavelet_eq,
    waveletRepresentative_setIntegral_zero]

private lemma coreWavelet_mul_integral (i j : WaveletIndex) :
    (∫ t in (0 : ℝ)..recordingWindow,
      coreWavelet i t * coreWavelet j t) =
        if i = j then 3 * recordingWindow / 16 else 0 := by
  cases i <;> cases j
  · simpa [coreWavelet, carrier, pow_two] using
      (hann_core_mul_cos_mode_sq_integral (k := 6) (by norm_num))
  · simpa [coreWavelet, carrier] using
      first_cos_sin_cross_integral
  · simpa [coreWavelet, carrier] using
      first_second_cos_cross_integral
  · calc
      (∫ t in (0 : ℝ)..recordingWindow,
          coreWavelet .sine30 t * coreWavelet .cosine30 t) =
          ∫ t in (0 : ℝ)..recordingWindow,
            coreWavelet .cosine30 t * coreWavelet .sine30 t := by
        apply intervalIntegral.integral_congr
        intro t _ht
        ring
      _ = 0 := by
        simpa [coreWavelet, carrier] using
          first_cos_sin_cross_integral
  · simpa [coreWavelet, carrier, pow_two] using
      (hann_core_mul_sin_mode_sq_integral (k := 6) (by norm_num))
  · simpa [coreWavelet, carrier] using
      first_sin_second_cos_cross_integral
  · calc
      (∫ t in (0 : ℝ)..recordingWindow,
          coreWavelet .cosine60 t * coreWavelet .cosine30 t) =
          ∫ t in (0 : ℝ)..recordingWindow,
            coreWavelet .cosine30 t * coreWavelet .cosine60 t := by
        apply intervalIntegral.integral_congr
        intro t _ht
        ring
      _ = 0 := by
        simpa [coreWavelet, carrier] using
          first_second_cos_cross_integral
  · calc
      (∫ t in (0 : ℝ)..recordingWindow,
          coreWavelet .cosine60 t * coreWavelet .sine30 t) =
          ∫ t in (0 : ℝ)..recordingWindow,
            coreWavelet .sine30 t * coreWavelet .cosine60 t := by
        apply intervalIntegral.integral_congr
        intro t _ht
        ring
      _ = 0 := by
        simpa [coreWavelet, carrier] using
          first_sin_second_cos_cross_integral
  · simpa [coreWavelet, carrier, pow_two] using
      (hann_core_mul_cos_mode_sq_integral (k := 12) (by norm_num))

private lemma normalization_sq_mul_raw_norm :
    normalization ^ 2 * (3 * recordingWindow / 16) = 1 := by
  unfold normalization recordingWindow
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 * (1 / 5))]
  norm_num

private lemma waveletRepresentative_product_setIntegral
    (i j : WaveletIndex) :
    (∫ t in Set.Icc (0 : ℝ) recordingWindow,
      waveletRepresentative i t * waveletRepresentative j t) =
        if i = j then 1 else 0 := by
  calc
    (∫ t in Set.Icc (0 : ℝ) recordingWindow,
        waveletRepresentative i t * waveletRepresentative j t) =
        ∫ t in Set.Icc (0 : ℝ) recordingWindow,
          normalization ^ 2 *
            (coreWavelet i t * coreWavelet j t) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only
      rw [waveletRepresentative_eq_on_window i ht,
        waveletRepresentative_eq_on_window j ht]
      ring
    _ = ∫ t in (0 : ℝ)..recordingWindow,
          normalization ^ 2 *
            (coreWavelet i t * coreWavelet j t) :=
      setIntegral_Icc_eq_intervalIntegral _
    _ = normalization ^ 2 *
          ∫ t in (0 : ℝ)..recordingWindow,
            coreWavelet i t * coreWavelet j t := by
      rw [intervalIntegral.integral_const_mul]
    _ = normalization ^ 2 *
          (if i = j then 3 * recordingWindow / 16 else 0) := by
      rw [coreWavelet_mul_integral]
    _ = if i = j then 1 else 0 := by
      split_ifs
      · exact normalization_sq_mul_raw_norm
      · ring

/-- The three-by-three Gram matrix is exactly the identity matrix. -/
theorem wavelet_gram (i j : WaveletIndex) :
    inner ℝ (wavelet i) (wavelet j) =
      if i = j then 1 else 0 := by
  rw [wavelet_inner_eq,
    waveletRepresentative_product_setIntegral]

/-- The paper's three wavelets form an orthonormal family in recording-window
`L²`. -/
theorem wavelet_orthonormal : Orthonormal ℝ wavelet := by
  rw [orthonormal_iff_ite]
  exact wavelet_gram

/-- Each paper wavelet has unit `L²` norm. -/
theorem wavelet_norm (i : WaveletIndex) :
    ‖wavelet i‖ = 1 :=
  wavelet_orthonormal.norm_eq_one i

/-- Distinct paper wavelets are pairwise orthogonal. -/
theorem wavelet_pairwise_orthogonal :
    Pairwise fun i j : WaveletIndex ↦
      inner ℝ (wavelet i) (wavelet j) = 0 :=
  wavelet_orthonormal.2

/-- The paper's first wavelet, `φ1`: a 30-Hz cosine carrier. -/
def phi1 : IPNPCNS.Signal.ScalarSignal recordingWindow :=
  wavelet .cosine30

/-- The paper's second wavelet, `φ2`: a 30-Hz sine carrier. -/
def phi2 : IPNPCNS.Signal.ScalarSignal recordingWindow :=
  wavelet .sine30

/-- The paper's third wavelet, `φ3`: a 60-Hz cosine carrier. -/
def phi3 : IPNPCNS.Signal.ScalarSignal recordingWindow :=
  wavelet .cosine60

/-- Synthesis by the two nonnegative input atoms `φ1` and `φ2`. -/
def twoWaveletSynthesis (a b : ℝ) :
    IPNPCNS.Signal.ScalarSignal recordingWindow :=
  a • phi1 + b • phi2

/-- A three-wavelet linear combination, used to state the third target. -/
def threeWaveletCombination (a b c : ℝ) :
    IPNPCNS.Signal.ScalarSignal recordingWindow :=
  a • phi1 + b • phi2 + c • phi3

private lemma twoWavelet_norm_sq (a b : ℝ) :
    ‖twoWaveletSynthesis a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [twoWaveletSynthesis, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, phi1, phi2, wavelet_gram]
  simp
  ring

private lemma threeWavelet_norm_sq (a b c : ℝ) :
    ‖threeWaveletCombination a b c‖ ^ 2 =
      a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [threeWaveletCombination, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, phi1, phi2, phi3, wavelet_gram]
  simp
  ring

private lemma twoWaveletSynthesis_sub (a b u v : ℝ) :
    twoWaveletSynthesis a b - twoWaveletSynthesis u v =
      twoWaveletSynthesis (a - u) (b - v) := by
  simp only [twoWaveletSynthesis]
  module

private lemma twoWaveletSynthesis_sub_three (a b u v c : ℝ) :
    twoWaveletSynthesis a b - threeWaveletCombination u v c =
      threeWaveletCombination (a - u) (b - v) (-c) := by
  simp only [twoWaveletSynthesis, threeWaveletCombination]
  module

/-- Squared `L²` error for the two-input synthesis model. -/
def squaredError
    (target : IPNPCNS.Signal.ScalarSignal recordingWindow) (a b : ℝ) : ℝ :=
  ‖twoWaveletSynthesis a b - target‖ ^ 2

/-- Feasibility for the example's two nonnegative synaptic weights. -/
def NonnegativePair (a b : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ b

/-- A feasible coefficient pair that globally minimizes the squared error over
all feasible pairs. -/
def IsNNLSMinimizer
    (target : IPNPCNS.Signal.ScalarSignal recordingWindow) (a b : ℝ) : Prop :=
  NonnegativePair a b ∧
    ∀ u v, NonnegativePair u v →
      squaredError target a b ≤ squaredError target u v

/-- Example 1 target: `y = φ1 + 2φ2`. -/
def exampleOneTarget : IPNPCNS.Signal.ScalarSignal recordingWindow :=
  twoWaveletSynthesis 1 2

/-- Exact Pythagorean loss formula for Example 1. -/
theorem example_one_error (a b : ℝ) :
    squaredError exampleOneTarget a b =
      (a - 1) ^ 2 + (b - 2) ^ 2 := by
  rw [squaredError, exampleOneTarget,
    twoWaveletSynthesis_sub, twoWavelet_norm_sq]

/-- The coefficients `(1,2)` reproduce the first target exactly. -/
theorem example_one_exact_fit :
    twoWaveletSynthesis 1 2 = exampleOneTarget := rfl

/-- The first example has the feasible NNLS solution `(1,2)`. -/
theorem example_one_nnls :
    IsNNLSMinimizer exampleOneTarget 1 2 := by
  constructor
  · exact ⟨by norm_num, by norm_num⟩
  · intro u v _huv
    rw [example_one_error, example_one_error]
    nlinarith [sq_nonneg (u - 1), sq_nonneg (v - 2)]

/-- Every NNLS minimizer for Example 1 equals `(1,2)`. -/
theorem example_one_unique (a b : ℝ)
    (h : IsNNLSMinimizer exampleOneTarget a b) :
    a = 1 ∧ b = 2 := by
  have hle := h.2 1 2 ⟨by norm_num, by norm_num⟩
  rw [example_one_error, example_one_error] at hle
  constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2)]

/-- Example 2 target: `y⁻ = φ1 - 2φ2`. -/
def exampleTwoTarget : IPNPCNS.Signal.ScalarSignal recordingWindow :=
  twoWaveletSynthesis 1 (-2)

/-- Exact constrained loss formula for Example 2. -/
theorem example_two_error (a b : ℝ) :
    squaredError exampleTwoTarget a b =
      (a - 1) ^ 2 + (b + 2) ^ 2 := by
  rw [squaredError, exampleTwoTarget,
    twoWaveletSynthesis_sub, twoWavelet_norm_sq]
  congr 1
  ring

/-- The nonnegative projection in Example 2 has coefficients `(1,0)`. -/
theorem example_two_nnls :
    IsNNLSMinimizer exampleTwoTarget 1 0 := by
  constructor
  · exact ⟨by norm_num, by norm_num⟩
  · intro u v huv
    rw [example_two_error, example_two_error]
    rcases huv with ⟨hu, hv⟩
    nlinarith [sq_nonneg (u - 1)]

/-- Every NNLS minimizer for Example 2 equals `(1,0)`. -/
theorem example_two_unique (a b : ℝ)
    (h : IsNNLSMinimizer exampleTwoTarget a b) :
    a = 1 ∧ b = 0 := by
  have hle := h.2 1 0 ⟨by norm_num, by norm_num⟩
  rw [example_two_error, example_two_error] at hle
  rcases h.1 with ⟨_ha, hb⟩
  constructor
  · nlinarith [sq_nonneg (a - 1)]
  · nlinarith [sq_nonneg (a - 1)]

/-- Target minus its two-wavelet approximation. -/
def approximationResidual
    (target : IPNPCNS.Signal.ScalarSignal recordingWindow) (a b : ℝ) :
    IPNPCNS.Signal.ScalarSignal recordingWindow :=
  target - twoWaveletSynthesis a b

/-- The paper's output sign convention: neuronal output is negative residual. -/
def neuronalOutput
    (target : IPNPCNS.Signal.ScalarSignal recordingWindow) (a b : ℝ) :
    IPNPCNS.Signal.ScalarSignal recordingWindow :=
  -approximationResidual target a b

/-- Example 2 leaves the polar residual `-2φ2`. -/
theorem example_two_residual :
    approximationResidual exampleTwoTarget 1 0 =
      (-2 : ℝ) • phi2 := by
  simp only [approximationResidual, exampleTwoTarget,
    twoWaveletSynthesis]
  module

/-- Example 2 consequently produces neuronal output `+2φ2`. -/
theorem example_two_output :
    neuronalOutput exampleTwoTarget 1 0 =
      (2 : ℝ) • phi2 := by
  rw [neuronalOutput, example_two_residual]
  module

/-- Example 3 target: `y⁺ = φ1 + 2φ2 + 3φ3`. -/
def exampleThreeTarget : IPNPCNS.Signal.ScalarSignal recordingWindow :=
  threeWaveletCombination 1 2 3

/-- Exact constrained loss formula for Example 3. -/
theorem example_three_error (a b : ℝ) :
    squaredError exampleThreeTarget a b =
      (a - 1) ^ 2 + (b - 2) ^ 2 + 9 := by
  rw [squaredError, exampleThreeTarget,
    twoWaveletSynthesis_sub_three, threeWavelet_norm_sq]
  norm_num

/-- The nonnegative projection in Example 3 has coefficients `(1,2)`. -/
theorem example_three_nnls :
    IsNNLSMinimizer exampleThreeTarget 1 2 := by
  constructor
  · exact ⟨by norm_num, by norm_num⟩
  · intro u v _huv
    rw [example_three_error, example_three_error]
    nlinarith [sq_nonneg (u - 1), sq_nonneg (v - 2)]

/-- Every NNLS minimizer for Example 3 equals `(1,2)`. -/
theorem example_three_unique (a b : ℝ)
    (h : IsNNLSMinimizer exampleThreeTarget a b) :
    a = 1 ∧ b = 2 := by
  have hle := h.2 1 2 ⟨by norm_num, by norm_num⟩
  rw [example_three_error, example_three_error] at hle
  constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2)]

/-- Example 3 leaves the orthogonal residual `+3φ3`. -/
theorem example_three_residual :
    approximationResidual exampleThreeTarget 1 2 =
      (3 : ℝ) • phi3 := by
  simp only [approximationResidual, exampleThreeTarget,
    twoWaveletSynthesis, threeWaveletCombination]
  module

/-- Example 3 consequently produces neuronal output `-3φ3`. -/
theorem example_three_output :
    neuronalOutput exampleThreeTarget 1 2 =
      (-3 : ℝ) • phi3 := by
  rw [neuronalOutput, example_three_residual]
  module

/-- A literal pointwise firing rate before baseline subtraction.  No
nonnegativity claim is made here: that depends on the chosen baseline and
amplitude, as it does in the paper. -/
def literalFiringRate (baseline amplitude : ℝ) (i : WaveletIndex) (t : ℝ) : ℝ :=
  baseline + amplitude * waveletRepresentative i t

/-- Remove a known constant baseline before interpreting a rate as an `L²`
modulation signal. -/
def subtractBaseline (baseline : ℝ) (rate : ℝ → ℝ) (t : ℝ) : ℝ :=
  rate t - baseline

/-- Baseline subtraction recovers exactly the modulation used by the
least-squares and inner-product calculations above. -/
@[simp]
theorem subtractBaseline_literalFiringRate
    (baseline amplitude : ℝ) (i : WaveletIndex) (t : ℝ) :
    subtractBaseline baseline (literalFiringRate baseline amplitude i) t =
      amplitude * waveletRepresentative i t := by
  simp [subtractBaseline, literalFiringRate]

end
end WaveletExample
end IPNPCNS
