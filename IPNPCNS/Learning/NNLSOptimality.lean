import IPNPCNS.Learning.NNLS
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Finite NNLS optimality

This module verifies the first-order meaning of the batch gradient in equation (39)
and proves that the complementarity conditions in equation (41) are equivalent to
global minimization of the finite nonnegative least-squares objective.
-/

open scoped BigOperators

namespace IPNPCNS

noncomputable section

variable {n N : ℕ}

/-- Euclidean coordinate pairing on a finite coefficient space. -/
def coefficientDot (u v : Fin n → ℝ) : ℝ :=
  ∑ i, u i * v i

theorem nnlsPrediction_add
    (X : Matrix (Fin n) (Fin N) ℝ) (w h : Fin n → ℝ) :
    nnlsPrediction X (w + h) = nnlsPrediction X w + nnlsPrediction X h := by
  funext j
  simp only [nnlsPrediction, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
    Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem nnlsPrediction_smul
    (X : Matrix (Fin n) (Fin N) ℝ) (t : ℝ) (h : Fin n → ℝ) :
    nnlsPrediction X (t • h) = t • nnlsPrediction X h := by
  funext j
  simp only [nnlsPrediction, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The coordinate pairing with the stated gradient equals the prediction-space
first-order term. -/
theorem coefficientDot_nnlsGradient
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (w h : Fin n → ℝ) :
    coefficientDot (nnlsGradient X y w) h =
      ∑ j, (nnlsPrediction X w j - y j) * nnlsPrediction X h j := by
  simp only [coefficientDot, nnlsGradient, nnlsPrediction, Matrix.mulVec,
    Matrix.transpose_apply, dotProduct, Pi.sub_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Exact first-order expansion of the finite NNLS quadratic. The final nonnegative
term is the convex quadratic remainder. -/
theorem nnlsLoss_add
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (w h : Fin n → ℝ) :
    nnlsLoss X y (w + h) = nnlsLoss X y w +
      coefficientDot (nnlsGradient X y w) h +
      (1 / 2 : ℝ) * ∑ j, (nnlsPrediction X h j) ^ 2 := by
  rw [coefficientDot_nnlsGradient]
  unfold nnlsLoss
  rw [nnlsPrediction_add]
  simp only [Pi.add_apply]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem coefficientDot_smul_right (u h : Fin n → ℝ) (t : ℝ) :
    coefficientDot u (t • h) = t * coefficientDot u h := by
  simp only [coefficientDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem nnlsPrediction_energy_smul
    (X : Matrix (Fin n) (Fin N) ℝ) (h : Fin n → ℝ) (t : ℝ) :
    (∑ j, (nnlsPrediction X (t • h) j) ^ 2) =
      t ^ 2 * ∑ j, (nnlsPrediction X h j) ^ 2 := by
  rw [nnlsPrediction_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.mul_sum]

/-- Scalar-line form of the first-order expansion. -/
theorem nnlsLoss_segment
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (w h : Fin n → ℝ) (t : ℝ) :
    nnlsLoss X y (w + t • h) = nnlsLoss X y w +
      t * coefficientDot (nnlsGradient X y w) h +
      t ^ 2 * ((1 / 2 : ℝ) * ∑ j, (nnlsPrediction X h j) ^ 2) := by
  rw [nnlsLoss_add, coefficientDot_smul_right, nnlsPrediction_energy_smul]
  ring

/-- Equation (39) is the directional derivative of equation (36) in every coefficient
direction. -/
theorem nnlsLoss_hasDerivAt_line
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (w h : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => nnlsLoss X y (w + t • h))
      (coefficientDot (nnlsGradient X y w) h) 0 := by
  have hid : ∀ t : ℝ,
      nnlsLoss X y (w + t • h) = nnlsLoss X y w +
        t * coefficientDot (nnlsGradient X y w) h +
        t ^ 2 * ((1 / 2 : ℝ) * ∑ j, (nnlsPrediction X h j) ^ 2) :=
    nnlsLoss_segment X y w h
  let A := coefficientDot (nnlsGradient X y w) h
  let B := (1 / 2 : ℝ) * ∑ j, (nnlsPrediction X h j) ^ 2
  have hlin : HasDerivAt (fun t : ℝ => t * A) A 0 := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id (x := (0 : ℝ))).mul_const A
  have hquad : HasDerivAt (fun t : ℝ => t ^ 2 * B) 0 0 := by
    have hraw := ((hasDerivAt_id (x := (0 : ℝ))).pow 2).mul_const B
    change HasDerivAt (fun t : ℝ => t ^ 2 * B)
      (2 * (0 : ℝ) ^ (2 - 1) * 1 * B) 0 at hraw
    norm_num at hraw ⊢
    exact hraw
  have hpoly : HasDerivAt
      (fun t : ℝ => nnlsLoss X y w + (t * A + t ^ 2 * B)) A 0 := by
    simpa only [Pi.add_apply, add_zero] using
      (hlin.add hquad).const_add (nnlsLoss X y w)
  apply hpoly.congr_of_eventuallyEq
  filter_upwards [] with t
  dsimp [A, B]
  simpa only [add_assoc] using hid t

/-- Global minimization of the batch loss over the nonnegative orthant. -/
def IsNNLSMinimizer
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (w : Fin n → ℝ) : Prop :=
  IsNonnegative w ∧
    ∀ v, IsNonnegative v → nnlsLoss X y w ≤ nnlsLoss X y v

private theorem linear_nonneg_of_quadratic_nonneg_on_unit {a q : ℝ}
    (hq : 0 ≤ q)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ t * a + t ^ 2 * q) :
    0 ≤ a := by
  by_contra ha
  have halt : a < 0 := lt_of_not_ge ha
  have hden : 0 < q + 1 := by linarith
  let t : ℝ := min (1 / 2 : ℝ) (-a / (q + 1))
  have htpos : 0 < t := lt_min (by norm_num) (div_pos (neg_pos.mpr halt) hden)
  have htone : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have htbound : t ≤ -a / (q + 1) := min_le_right _ _
  have hratio : (-a / (q + 1)) * q < -a := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith [mul_pos (neg_pos.mpr halt) hden]
  have htq : t * q < -a :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right htbound hq) hratio
  have hneg : t * a + t ^ 2 * q < 0 := by
    rw [show t * a + t ^ 2 * q = t * (a + t * q) by ring]
    exact mul_neg_of_pos_of_neg htpos (by linarith)
  exact (not_lt_of_ge (h t htpos.le htone)) hneg

/-- A global NNLS minimizer satisfies the first-order variational inequality against
every feasible point. -/
theorem nnls_firstOrder_nonneg_of_minimizer
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    {w v : Fin n → ℝ} (hw : IsNNLSMinimizer X y w)
    (hv : IsNonnegative v) :
    0 ≤ coefficientDot (nnlsGradient X y w) (v - w) := by
  let q : ℝ := (1 / 2 : ℝ) * ∑ j, (nnlsPrediction X (v - w) j) ^ 2
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  apply linear_nonneg_of_quadratic_nonneg_on_unit hq
  intro t ht ht1
  have hfeas : IsNonnegative (w + t • (v - w)) := by
    intro i
    have hwi := hw.1 i
    have hvi := hv i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    nlinarith
  have hmin := hw.2 (w + t • (v - w)) hfeas
  rw [nnlsLoss_segment] at hmin
  dsimp [q]
  nlinarith

/-- A coordinate unit vector in coefficient space. -/
def coordinateUnit (i : Fin n) : Fin n → ℝ :=
  fun j => if j = i then 1 else 0

theorem coefficientDot_coordinateUnit (u : Fin n → ℝ) (i : Fin n) :
    coefficientDot u (coordinateUnit i) = u i := by
  simp [coefficientDot, coordinateUnit]

/-- Global NNLS optimality implies complementarity. -/
theorem complementaryKKT_of_nnlsMinimizer
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    {w : Fin n → ℝ} (hw : IsNNLSMinimizer X y w) :
    ComplementaryKKT w (nnlsGradient X y w) := by
  let g := nnlsGradient X y w
  have hg : IsNonnegative g := by
    intro i
    let v := w + coordinateUnit i
    have hv : IsNonnegative v := by
      intro j
      have hwj := hw.1 j
      by_cases hji : j = i
      · subst j
        simp [v, coordinateUnit]
        linarith
      · simp [v, coordinateUnit, hji, hwj]
    have hvar := nnls_firstOrder_nonneg_of_minimizer X y hw hv
    have hvsub : v - w = coordinateUnit i := by
      funext j
      simp [v]
    rw [hvsub, coefficientDot_coordinateUnit] at hvar
    exact hvar
  have hzero : IsNonnegative (0 : Fin n → ℝ) := fun i => le_rfl
  have hvar0 := nnls_firstOrder_nonneg_of_minimizer X y hw hzero
  have hsumle : ∑ i, w i * g i ≤ 0 := by
    dsimp [g] at hvar0 ⊢
    unfold coefficientDot at hvar0
    simp only [Pi.zero_apply, Pi.sub_apply, zero_sub] at hvar0
    have heq : (∑ i, nnlsGradient X y w i * -w i) =
        -(∑ i, w i * nnlsGradient X y w i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq] at hvar0
    linarith
  have hterms : ∀ i ∈ Finset.univ, 0 ≤ w i * g i := by
    intro i hi
    exact mul_nonneg (hw.1 i) (hg i)
  have hsumeq : ∑ i, w i * g i = 0 :=
    le_antisymm hsumle (Finset.sum_nonneg hterms)
  have hcomp : ∀ i, w i * g i = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsumeq i
      (Finset.mem_univ i)
  exact ⟨hw.1, hg, hcomp⟩

/-- Complementarity is sufficient for global NNLS optimality because the loss has a
nonnegative quadratic remainder. -/
theorem nnlsMinimizer_of_complementaryKKT
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    {w : Fin n → ℝ}
    (hw : ComplementaryKKT w (nnlsGradient X y w)) :
    IsNNLSMinimizer X y w := by
  refine ⟨hw.1, ?_⟩
  intro v hv
  have hdot : 0 ≤ coefficientDot (nnlsGradient X y w) (v - w) := by
    unfold coefficientDot
    apply Finset.sum_nonneg
    intro i hi
    calc
      nnlsGradient X y w i * (v - w) i =
          nnlsGradient X y w i * v i - w i * nnlsGradient X y w i := by
        simp only [Pi.sub_apply]
        ring
      _ = nnlsGradient X y w i * v i := by rw [hw.2.2 i, sub_zero]
      _ ≥ 0 := mul_nonneg (hw.2.1 i) (hv i)
  have hrem : 0 ≤ (1 / 2 : ℝ) *
      ∑ j, (nnlsPrediction X (v - w) j) ^ 2 := by positivity
  have heq := nnlsLoss_add X y w (v - w)
  have hadd : w + (v - w) = v := by
    funext i
    simp
  rw [hadd] at heq
  nlinarith

/-- Finite convex NNLS: global minimizers are exactly the complementary KKT points. -/
theorem nnlsMinimizer_iff_complementaryKKT
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (w : Fin n → ℝ) :
    IsNNLSMinimizer X y w ↔
      ComplementaryKKT w (nnlsGradient X y w) :=
  ⟨complementaryKKT_of_nnlsMinimizer X y,
    nnlsMinimizer_of_complementaryKKT X y⟩

end

end IPNPCNS
