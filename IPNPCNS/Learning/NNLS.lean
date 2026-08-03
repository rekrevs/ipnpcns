import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Linarith

/-!
# Finite nonnegative least squares

This module formalizes equations (36), (39), (40), and (41) at the finite
componentwise level. It deliberately does not infer stochastic convergence from the
paper's phrase "standard assumptions".
-/

open scoped BigOperators

namespace IPNPCNS

noncomputable section

variable {n N : ℕ}

/-- The nonnegative orthant used by the NNLS problem. -/
def IsNonnegative (w : Fin n → ℝ) : Prop :=
  ∀ i, 0 ≤ w i

/-- The prediction `Xᵀw` in equation (36). -/
def nnlsPrediction (X : Matrix (Fin n) (Fin N) ℝ) (w : Fin n → ℝ) :
    Fin N → ℝ :=
  X.transpose.mulVec w

/-- The batch objective in equation (36). -/
def nnlsLoss (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (w : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, (nnlsPrediction X w j - y j) ^ 2

/-- The batch-gradient formula in equation (39). -/
def nnlsGradient (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ)
    (w : Fin n → ℝ) : Fin n → ℝ :=
  X.mulVec (nnlsPrediction X w - y)

/-- Euclidean projection onto the nonnegative orthant. -/
def positivePart (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => max 0 (w i)

/-- The projected batch update in equation (40). -/
def projectedUpdate (ε : ℝ) (g w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => max 0 (w i - ε * g i)

/-- The complementarity conditions in equation (41). -/
def ComplementaryKKT (w g : Fin n → ℝ) : Prop :=
  IsNonnegative w ∧ IsNonnegative g ∧ ∀ i, w i * g i = 0

private theorem scalar_projected_fixed_iff {ε w g : ℝ} (hε : 0 < ε) :
    max 0 (w - ε * g) = w ↔
      0 ≤ w ∧ 0 ≤ g ∧ w * g = 0 := by
  constructor
  · intro h
    have hw : 0 ≤ w := by
      rw [← h]
      exact le_max_left 0 (w - ε * g)
    by_cases hw0 : w = 0
    · subst w
      have harg : -ε * g ≤ 0 := by
        apply max_eq_left_iff.mp
        simpa using h
      exact ⟨le_rfl, by nlinarith, by simp⟩
    · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
      have harg : 0 ≤ w - ε * g := by
        by_contra hneg
        have hmax : max 0 (w - ε * g) = 0 :=
          max_eq_left (le_of_not_ge hneg)
        rw [hmax] at h
        linarith
      have heq : w - ε * g = w := by
        rw [max_eq_right harg] at h
        exact h
      have hg : g = 0 := by nlinarith
      exact ⟨hw, by simp [hg], by simp [hg]⟩
  · rintro ⟨hw, hg, hcomp⟩
    by_cases hw0 : w = 0
    · subst w
      apply max_eq_left
      nlinarith
    · have hg0 : g = 0 := by
        exact (mul_eq_zero.mp hcomp).resolve_left hw0
      simp [hg0, max_eq_right hw]

/-- Equations (40)–(41): fixed points of a positive-step projected update are exactly
the componentwise KKT/complementarity points. -/
theorem projectedUpdate_fixed_iff_kkt
    {ε : ℝ} (hε : 0 < ε) (g w : Fin n → ℝ) :
    projectedUpdate ε g w = w ↔ ComplementaryKKT w g := by
  constructor
  · intro h
    have hi : ∀ i, max 0 (w i - ε * g i) = w i := fun i => congrFun h i
    refine ⟨fun i => (scalar_projected_fixed_iff hε |>.mp (hi i)).1,
      fun i => (scalar_projected_fixed_iff hε |>.mp (hi i)).2.1,
      fun i => (scalar_projected_fixed_iff hε |>.mp (hi i)).2.2⟩
  · rintro ⟨hw, hg, hcomp⟩
    funext i
    exact (scalar_projected_fixed_iff hε).mpr ⟨hw i, hg i, hcomp i⟩

/-- The full-batch specialization of equations (40)–(41). -/
theorem projectedBatchUpdate_fixed_iff_kkt
    {ε : ℝ} (hε : 0 < ε)
    (X : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ) (w : Fin n → ℝ) :
    projectedUpdate ε (nnlsGradient X y w) w = w ↔
      ComplementaryKKT w (nnlsGradient X y w) :=
  projectedUpdate_fixed_iff_kkt hε _ _

end

end IPNPCNS
