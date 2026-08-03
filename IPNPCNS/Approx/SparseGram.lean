import IPNPCNS.Approx.Polarization
import Mathlib.Algebra.Order.Chebyshev

/-!
# Sparse Gram bounds

This module formalizes the deterministic collateral-branching calculation in
equations (170) and (171). A finite active set selects columns from an arbitrary real
inner-product space. Diagonal gain error and off-diagonal coherence imply the sharp
`η + (k - 1) μ` quadratic bound. No random-matrix claim is used.
-/

open scoped BigOperators

namespace IPNPCNS

noncomputable section

variable {ι H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The Gram matrix of a family of transmission columns. -/
def columnGram (m : ι → H) : Matrix ι ι ℝ :=
  fun i j => inner ℝ (m i) (m j)

/-- The finite Gram submatrix selected by an active set. -/
def activeColumnGram (m : ι → H) (s : Finset ι) : Matrix s s ℝ :=
  fun i j => columnGram m i j

@[simp]
theorem activeColumnGram_apply (m : ι → H) (s : Finset ι) (i j : s) :
    activeColumnGram m s i j = inner ℝ (m i) (m j) :=
  rfl

/-- The transmitted vector formed by the active columns. -/
def activeColumnCombination (m : ι → H) (s : Finset ι) (x : ι → ℝ) : H :=
  ∑ i ∈ s, x i • m i

/-- The squared Euclidean coefficient norm on the active set. -/
def activeCoefficientEnergy (s : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, x i ^ 2

/-- Expansion of the transmitted squared norm through the finite active Gram matrix. -/
theorem norm_activeColumnCombination_sq
    (m : ι → H) (s : Finset ι) (x : ι → ℝ) :
    ‖activeColumnCombination m s x‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s,
        x i * x j * columnGram m i j := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [activeColumnCombination, columnGram, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, conj_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm (m j) (m i)]
  ring

/-- Equation (170): normalized diagonal gain and pairwise coherence hypotheses. -/
structure ColumnBounds170 (m : ι → H) (α η μ : ℝ) : Prop where
  diagonal : ∀ i, |columnGram m i i / α - 1| ≤ η
  offDiagonal : ∀ i j, i ≠ j → |columnGram m i j / α| ≤ μ

theorem ColumnBounds170.diagonal_scaled
    {m : ι → H} {α η μ : ℝ}
    (h : ColumnBounds170 m α η μ) (hα : 0 < α) (i : ι) :
    |inner ℝ (m i) (m i) - α| ≤ η * α := by
  have hi := h.diagonal i
  simp only [columnGram] at hi
  have heq : inner ℝ (m i) (m i) / α - 1 =
      (inner ℝ (m i) (m i) - α) / α := by
    field_simp
  rw [heq, abs_div, abs_of_pos hα] at hi
  exact (div_le_iff₀ hα).mp hi

theorem ColumnBounds170.offDiagonal_scaled
    {m : ι → H} {α η μ : ℝ}
    (h : ColumnBounds170 m α η μ) (hα : 0 < α)
    {i j : ι} (hij : i ≠ j) :
    |inner ℝ (m i) (m j)| ≤ μ * α := by
  have hi := h.offDiagonal i j hij
  simp only [columnGram, abs_div, abs_of_pos hα] at hi
  exact (div_le_iff₀ hα).mp hi

/-- The diagonal part of the active quadratic-form error. -/
def activeDiagonalError
    (m : ι → H) (α : ℝ) (s : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, x i ^ 2 * (inner ℝ (m i) (m i) - α)

private theorem abs_activeDiagonalError_le
    (m : ι → H) (α η : ℝ) (s : Finset ι) (x : ι → ℝ)
    (hdiag : ∀ i ∈ s, |inner ℝ (m i) (m i) - α| ≤ η * α) :
    |activeDiagonalError m α s x| ≤
      η * α * activeCoefficientEnergy s x := by
  calc
    |activeDiagonalError m α s x| ≤
        ∑ i ∈ s, |x i ^ 2 * (inner ℝ (m i) (m i) - α)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, x i ^ 2 * (η * α) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (sq_nonneg (x i))]
      exact mul_le_mul_of_nonneg_left (hdiag i hi) (sq_nonneg (x i))
    _ = η * α * activeCoefficientEnergy s x := by
      simp only [activeCoefficientEnergy]
      rw [← Finset.sum_mul]
      ring

section DecidableIndex

variable [DecidableEq ι]

/-- The absolute coefficient mass over ordered distinct active pairs. -/
def offDiagonalCoefficientMass (s : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s.erase i, |x i| * |x j|

/-- Counting distinct neighbours and using `2ab ≤ a² + b²` gives the exact
`card s - 1` coefficient. -/
theorem offDiagonalCoefficientMass_le
    (s : Finset ι) (x : ι → ℝ) :
    offDiagonalCoefficientMass s x ≤
      ((s.card - 1 : ℕ) : ℝ) * activeCoefficientEnergy s x := by
  by_cases hs : s = ∅
  · subst s
    simp [offDiagonalCoefficientMass, activeCoefficientEnergy]
  have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
  have hcard : 1 ≤ s.card :=
    Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hsne)
  let c : ℝ := ((s.card - 1 : ℕ) : ℝ)
  let E : ℝ := activeCoefficientEnergy s x
  have hc : c = (s.card : ℝ) - 1 := by
    dsimp [c]
    rw [Nat.cast_sub hcard]
    norm_num
  have hfirst :
      (∑ i ∈ s, ∑ _j ∈ s.erase i, x i ^ 2) = c * E := by
    calc
      (∑ i ∈ s, ∑ _j ∈ s.erase i, x i ^ 2) =
          ∑ i ∈ s, ((s.erase i).card : ℝ) * x i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp
      _ = ∑ i ∈ s, c * x i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.card_erase_of_mem hi]
      _ = c * E := by
        simp only [E, activeCoefficientEnergy, Finset.mul_sum]
  have hsecond :
      (∑ i ∈ s, ∑ j ∈ s.erase i, x j ^ 2) = c * E := by
    have hrow : ∀ i ∈ s,
        (∑ j ∈ s.erase i, x j ^ 2) = E - x i ^ 2 := by
      intro i hi
      dsimp [E, activeCoefficientEnergy]
      linarith only [Finset.sum_erase_add s (fun j => x j ^ 2) hi]
    calc
      (∑ i ∈ s, ∑ j ∈ s.erase i, x j ^ 2) =
          ∑ i ∈ s, (E - x i ^ 2) := by
        exact Finset.sum_congr rfl hrow
      _ = (s.card : ℝ) * E - E := by
        simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
          E, activeCoefficientEnergy]
      _ = c * E := by rw [hc]; ring
  have htwice : 2 * offDiagonalCoefficientMass s x ≤
      ∑ i ∈ s, ∑ j ∈ s.erase i, (x i ^ 2 + x j ^ 2) := by
    simp only [offDiagonalCoefficientMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    simpa only [mul_assoc, sq_abs] using two_mul_le_add_sq |x i| |x j|
  have hrhs :
      (∑ i ∈ s, ∑ j ∈ s.erase i, (x i ^ 2 + x j ^ 2)) =
        2 * c * E := by
    calc
      (∑ i ∈ s, ∑ j ∈ s.erase i, (x i ^ 2 + x j ^ 2)) =
          (∑ i ∈ s, ∑ _j ∈ s.erase i, x i ^ 2) +
            (∑ i ∈ s, ∑ j ∈ s.erase i, x j ^ 2) := by
        simp only [Finset.sum_add_distrib]
      _ = 2 * c * E := by rw [hfirst, hsecond]; ring
  rw [hrhs] at htwice
  nlinarith

/-- The off-diagonal part of the active Gram quadratic form. -/
def activeOffDiagonalInner
    (m : ι → H) (s : Finset ι) (x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s.erase i, x i * x j * inner ℝ (m i) (m j)

private theorem active_distortion_eq
    (m : ι → H) (α : ℝ) (s : Finset ι) (x : ι → ℝ) :
    ‖activeColumnCombination m s x‖ ^ 2 -
        α * activeCoefficientEnergy s x =
      activeDiagonalError m α s x + activeOffDiagonalInner m s x := by
  rw [norm_activeColumnCombination_sq]
  have hsplit :
      (∑ i ∈ s, ∑ j ∈ s,
          x i * x j * columnGram m i j) =
        (∑ i ∈ s, x i ^ 2 * inner ℝ (m i) (m i)) +
          activeOffDiagonalInner m s x := by
    simp only [columnGram, activeOffDiagonalInner]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hrow := Finset.sum_erase_add s
      (fun j => x i * x j * inner ℝ (m i) (m j)) hi
    rw [← hrow, add_comm]
    congr 1
    ring
  rw [hsplit]
  simp only [activeDiagonalError, activeCoefficientEnergy]
  rw [Finset.mul_sum]
  have hsums :
      (∑ i ∈ s, x i ^ 2 * inner ℝ (m i) (m i)) -
          (∑ i ∈ s, α * x i ^ 2) =
        ∑ i ∈ s, x i ^ 2 * (inner ℝ (m i) (m i) - α) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [show (∑ i ∈ s, x i ^ 2 * inner ℝ (m i) (m i)) +
      activeOffDiagonalInner m s x - (∑ i ∈ s, α * x i ^ 2) =
      ((∑ i ∈ s, x i ^ 2 * inner ℝ (m i) (m i)) -
        (∑ i ∈ s, α * x i ^ 2)) + activeOffDiagonalInner m s x by ring, hsums]

private theorem abs_activeOffDiagonalInner_le
    (m : ι → H) (α μ : ℝ) (s : Finset ι) (x : ι → ℝ)
    (hμα : 0 ≤ μ * α)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      |inner ℝ (m i) (m j)| ≤ μ * α) :
    |activeOffDiagonalInner m s x| ≤
      μ * α * ((s.card - 1 : ℕ) : ℝ) * activeCoefficientEnergy s x := by
  have hraw : |activeOffDiagonalInner m s x| ≤
      μ * α * offDiagonalCoefficientMass s x := by
    calc
      |activeOffDiagonalInner m s x| ≤
          ∑ i ∈ s, |∑ j ∈ s.erase i,
            x i * x j * inner ℝ (m i) (m j)| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, ∑ j ∈ s.erase i,
          |x i * x j * inner ℝ (m i) (m j)| := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, ∑ j ∈ s.erase i,
          (μ * α) * (|x i| * |x j|) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have hjs : j ∈ s := Finset.mem_of_mem_erase hj
        have hne : i ≠ j := fun hij => (Finset.ne_of_mem_erase hj) hij.symm
        rw [abs_mul, abs_mul]
        calc
          |x i| * |x j| * |inner ℝ (m i) (m j)| ≤
              |x i| * |x j| * (μ * α) :=
            mul_le_mul_of_nonneg_left (hoff i hi j hjs hne)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = (μ * α) * (|x i| * |x j|) := by ring
      _ = μ * α * offDiagonalCoefficientMass s x := by
        simp only [offDiagonalCoefficientMass, Finset.mul_sum]
  calc
    |activeOffDiagonalInner m s x| ≤
        μ * α * offDiagonalCoefficientMass s x := hraw
    _ ≤ μ * α *
        (((s.card - 1 : ℕ) : ℝ) * activeCoefficientEnergy s x) :=
      mul_le_mul_of_nonneg_left (offDiagonalCoefficientMass_le s x) hμα
    _ = μ * α * ((s.card - 1 : ℕ) : ℝ) *
        activeCoefficientEnergy s x := by ring

/-- Absolute quadratic-form version of equation (171) for the exact active-cardinality
constant. -/
theorem abs_activeGram_distortion_le
    (m : ι → H) (α η μ : ℝ) (s : Finset ι) (x : ι → ℝ)
    (hμα : 0 ≤ μ * α)
    (hdiag : ∀ i ∈ s, |inner ℝ (m i) (m i) - α| ≤ η * α)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      |inner ℝ (m i) (m j)| ≤ μ * α) :
    |‖activeColumnCombination m s x‖ ^ 2 -
        α * activeCoefficientEnergy s x| ≤
      (η + ((s.card - 1 : ℕ) : ℝ) * μ) * α *
        activeCoefficientEnergy s x := by
  rw [active_distortion_eq]
  calc
    |activeDiagonalError m α s x + activeOffDiagonalInner m s x| ≤
        |activeDiagonalError m α s x| + |activeOffDiagonalInner m s x| :=
      abs_add_le _ _
    _ ≤ η * α * activeCoefficientEnergy s x +
        μ * α * ((s.card - 1 : ℕ) : ℝ) * activeCoefficientEnergy s x :=
      add_le_add (abs_activeDiagonalError_le m α η s x hdiag)
        (abs_activeOffDiagonalInner_le m α μ s x hμα hoff)
    _ = (η + ((s.card - 1 : ℕ) : ℝ) * μ) * α *
        activeCoefficientEnergy s x := by ring

/-- Equation (171) with `ρ = η + (card s - 1) μ`. -/
theorem activeGramRIP171
    (m : ι → H) (α η μ : ℝ) (s : Finset ι) (x : ι → ℝ)
    (h : ColumnBounds170 m α η μ)
    (hα : 0 < α) (hη : 0 ≤ η) (hμ : 0 ≤ μ) :
    let ρ := η + ((s.card - 1 : ℕ) : ℝ) * μ
    (1 - ρ) * α * activeCoefficientEnergy s x ≤
        ‖activeColumnCombination m s x‖ ^ 2 ∧
      ‖activeColumnCombination m s x‖ ^ 2 ≤
        (1 + ρ) * α * activeCoefficientEnergy s x := by
  dsimp only
  have herr := abs_activeGram_distortion_le m α η μ s x
    (mul_nonneg hμ hα.le)
    (fun i _ => h.diagonal_scaled hα i)
    (fun i _ j _ hij => h.offDiagonal_scaled hα hij)
  have hρ : 0 ≤ η + ((s.card - 1 : ℕ) : ℝ) * μ :=
    add_nonneg hη (mul_nonneg (Nat.cast_nonneg _) hμ)
  rw [abs_le] at herr
  constructor <;> nlinarith

/-- Equation (171) for an active set of cardinality at most `k`. The natural-number
subtraction makes the `k = 0` coefficient explicit and equal to zero. -/
theorem sparseGramRIP171_of_card_le
    (m : ι → H) (α η μ : ℝ) (s : Finset ι) (x : ι → ℝ)
    (k : ℕ) (hcard : s.card ≤ k)
    (h : ColumnBounds170 m α η μ)
    (hα : 0 < α) (hη : 0 ≤ η) (hμ : 0 ≤ μ) :
    let ρk := η + ((k - 1 : ℕ) : ℝ) * μ
    (1 - ρk) * α * activeCoefficientEnergy s x ≤
        ‖activeColumnCombination m s x‖ ^ 2 ∧
      ‖activeColumnCombination m s x‖ ^ 2 ≤
        (1 + ρk) * α * activeCoefficientEnergy s x := by
  dsimp only
  have herr := abs_activeGram_distortion_le m α η μ s x
    (mul_nonneg hμ hα.le)
    (fun i _ => h.diagonal_scaled hα i)
    (fun i _ j _ hij => h.offDiagonal_scaled hα hij)
  have hcNat : s.card - 1 ≤ k - 1 := Nat.sub_le_sub_right hcard 1
  have hc : ((s.card - 1 : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast hcNat
  have hcoef : η + ((s.card - 1 : ℕ) : ℝ) * μ ≤
      η + ((k - 1 : ℕ) : ℝ) * μ := by
    gcongr
  have hE : 0 ≤ activeCoefficientEnergy s x :=
    Finset.sum_nonneg fun i hi => sq_nonneg (x i)
  have hscale :
      (η + ((s.card - 1 : ℕ) : ℝ) * μ) * α * activeCoefficientEnergy s x ≤
        (η + ((k - 1 : ℕ) : ℝ) * μ) * α * activeCoefficientEnergy s x := by
    gcongr
  have herr' := herr.trans hscale
  have hρ : 0 ≤ η + ((k - 1 : ℕ) : ℝ) * μ :=
    add_nonneg hη (mul_nonneg (Nat.cast_nonneg _) hμ)
  rw [abs_le] at herr'
  constructor <;> nlinarith

omit [DecidableEq ι] in
/-- At order zero, the cardinality hypothesis forces the active set to be empty. -/
theorem activeSet_eq_empty_of_card_le_zero
    (s : Finset ι) (hcard : s.card ≤ 0) : s = ∅ :=
  Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)

end DecidableIndex

end

end IPNPCNS
