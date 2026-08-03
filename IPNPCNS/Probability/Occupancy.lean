import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp

/-!
# Finite collateral occupancy

This module formalizes the exact part of equation (30).  One active axon selects a
uniform `p`-element subset of `n` targets; an `m`-axon sample is an element of the
finite Cartesian power of that choice set, so independence across axons is built into
the uniform product average.  The exponential replacement receives a quantitative
error theorem. The additional two-message independence premise is realized by a
separate product experiment but is not inferred for biological messages.
-/

open scoped BigOperators

namespace IPNPCNS

noncomputable section

/-- The possible distinct collateral target sets for one axon. -/
def collateralChoices (n p : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard p

/-- The product sample space for `m` independently and uniformly selected collateral
sets. -/
def occupancySamples (n m p : ℕ) : Finset (Fin m → Finset (Fin n)) :=
  Fintype.piFinset (fun _ : Fin m => collateralChoices n p)

/-- Targets reached by at least one active axon in a sample. -/
def occupiedTargets {n m : ℕ} (sample : Fin m → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun target => ∃ axon, target ∈ sample axon

/-- Number of occupied targets in one sample. -/
def occupiedCount {n m : ℕ} (sample : Fin m → Finset (Fin n)) : ℕ :=
  (occupiedTargets sample).card

/-- Uniform expected occupancy in the exact finite experiment. -/
def expectedOccupied (n m p : ℕ) : ℝ :=
  𝔼 sample ∈ occupancySamples n m p, (occupiedCount sample : ℝ)

/-- The exact expression in equation (30). -/
def exactOccupancyFormula (n m p : ℕ) : ℝ :=
  (n : ℝ) * (1 - (1 - (p : ℝ) / (n : ℝ)) ^ m)

/-- Indicator that one axon's collateral set misses a target. -/
def localMissIndicator {n : ℕ} (target : Fin n) (selection : Finset (Fin n)) : ℝ :=
  if target ∉ selection then 1 else 0

/-- Indicator that every active axon misses a target. -/
def sampleMissIndicator {n m : ℕ} (sample : Fin m → Finset (Fin n))
    (target : Fin n) : ℝ :=
  ∏ axon, localMissIndicator target (sample axon)

/-- Indicator that at least one active axon reaches a target. -/
def targetOccupiedIndicator {n m : ℕ} (sample : Fin m → Finset (Fin n))
    (target : Fin n) : ℝ :=
  1 - sampleMissIndicator sample target

theorem collateralChoices_nonempty {n p : ℕ} (hp : p ≤ n) :
    (collateralChoices n p).Nonempty := by
  rw [collateralChoices, Finset.powersetCard_nonempty]
  simpa using hp

theorem mem_collateralChoices_iff {n p : ℕ} {selection : Finset (Fin n)} :
    selection ∈ collateralChoices n p ↔ selection.card = p := by
  simp [collateralChoices, Finset.mem_powersetCard]

theorem mem_occupancySamples_iff {n m p : ℕ}
    {sample : Fin m → Finset (Fin n)} :
    sample ∈ occupancySamples n m p ↔
      ∀ axon, (sample axon).card = p := by
  simp [occupancySamples, mem_collateralChoices_iff]

theorem occupancySamples_nonempty {n m p : ℕ} (hp : p ≤ n) :
    (occupancySamples n m p).Nonempty := by
  exact (collateralChoices_nonempty hp).piFinset_const

theorem collateralChoices_eq_empty_iff {n p : ℕ} :
    collateralChoices n p = ∅ ↔ n < p := by
  simp [collateralChoices, Finset.powersetCard_eq_empty]

private theorem missChoices_eq (n p : ℕ) (target : Fin n) :
    (collateralChoices n p).filter (fun s => target ∉ s) =
      ((Finset.univ : Finset (Fin n)).erase target).powersetCard p := by
  ext s
  simp [collateralChoices, Finset.subset_erase, and_comm]

theorem card_missChoices (n p : ℕ) (target : Fin n) :
    ((collateralChoices n p).filter (fun s => target ∉ s)).card =
      Nat.choose (n - 1) p := by
  rw [missChoices_eq, Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_univ target), Finset.card_univ,
    Fintype.card_fin]

theorem card_collateralChoices (n p : ℕ) :
    (collateralChoices n p).card = Nat.choose n p := by
  simp [collateralChoices, Finset.card_powersetCard]

/-- The exact one-axon miss probability under uniform selection without replacement. -/
theorem localMissExpectation {n p : ℕ} (hn : 0 < n) (hp : p ≤ n)
    (target : Fin n) :
    (𝔼 s ∈ collateralChoices n p, if target ∉ s then (1 : ℝ) else 0) =
      1 - (p : ℝ) / (n : ℝ) := by
  rw [Finset.expect_eq_sum_div_card]
  have hsum :
      (∑ s ∈ collateralChoices n p, if target ∉ s then (1 : ℝ) else 0) =
        (((collateralChoices n p).filter (fun s => target ∉ s)).card : ℝ) := by
    exact Finset.sum_boole (R := ℝ) (fun s => target ∉ s) _
  rw [hsum, card_missChoices, card_collateralChoices]
  have hn1 : 1 ≤ n := hn
  have hchooseNat :
      Nat.choose (n - 1) p * n = Nat.choose n p * (n - p) := by
    simpa [Nat.sub_add_cancel hn1] using Nat.choose_mul_succ_eq (n - 1) p
  have hchooseReal :
      (Nat.choose (n - 1) p : ℝ) * (n : ℝ) =
        (Nat.choose n p : ℝ) * (n - p : ℕ) := by
    exact_mod_cast hchooseNat
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hchoose0 : (Nat.choose n p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hp).ne'
  calc
    (Nat.choose (n - 1) p : ℝ) / Nat.choose n p =
        (n - p : ℕ) / (n : ℝ) := by
      apply (div_eq_div_iff hchoose0 hn0).2
      simpa [mul_comm] using hchooseReal
    _ = 1 - (p : ℝ) / (n : ℝ) := by
      rw [Nat.cast_sub hp]
      field_simp

theorem targetOccupiedIndicator_eq {n m : ℕ}
    (sample : Fin m → Finset (Fin n)) (target : Fin n) :
    targetOccupiedIndicator sample target =
      if target ∈ occupiedTargets sample then 1 else 0 := by
  classical
  by_cases hHit : ∃ axon, target ∈ sample axon
  · obtain ⟨axon, haxon⟩ := hHit
    have hOccupied : target ∈ occupiedTargets sample := by
      simp [occupiedTargets]
      exact ⟨axon, haxon⟩
    have hmiss : sampleMissIndicator sample target = 0 := by
      unfold sampleMissIndicator
      apply Finset.prod_eq_zero (Finset.mem_univ axon)
      simp [localMissIndicator, haxon]
    rw [if_pos hOccupied]
    simp [targetOccupiedIndicator, hmiss]
  · have hmiss : sampleMissIndicator sample target = 1 := by
      unfold sampleMissIndicator
      apply Finset.prod_eq_one
      intro axon _hmem
      have hnot : target ∉ sample axon := fun haxon => hHit ⟨axon, haxon⟩
      simp [localMissIndicator, hnot]
    simp [targetOccupiedIndicator, occupiedTargets, hmiss, hHit]

theorem cast_occupiedCount_eq_sum_indicators {n m : ℕ}
    (sample : Fin m → Finset (Fin n)) :
    (occupiedCount sample : ℝ) = ∑ target, targetOccupiedIndicator sample target := by
  classical
  calc
    (occupiedCount sample : ℝ) =
        ∑ target ∈ (Finset.univ : Finset (Fin n)),
          if target ∈ occupiedTargets sample then (1 : ℝ) else 0 := by
      rw [occupiedCount, Finset.sum_boole]
      congr 2
      ext target
      simp [occupiedTargets]
    _ = ∑ target, targetOccupiedIndicator sample target := by
      apply Finset.sum_congr rfl
      intro target _htarget
      exact (targetOccupiedIndicator_eq sample target).symm

/-- Product sampling makes the all-miss probability the `m`th power of the local
miss probability. -/
theorem sampleMissExpectation {n m p : ℕ} (hn : 0 < n) (hp : p ≤ n)
    (target : Fin n) :
    (𝔼 sample ∈ occupancySamples n m p, sampleMissIndicator sample target) =
      (1 - (p : ℝ) / (n : ℝ)) ^ m := by
  have hpow := Finset.expect_pow (collateralChoices n p)
    (fun selection => localMissIndicator target selection) m
  unfold localMissIndicator at hpow
  rw [localMissExpectation hn hp target] at hpow
  simpa [occupancySamples, sampleMissIndicator, localMissIndicator] using hpow.symm

theorem targetOccupiedExpectation {n m p : ℕ} (hn : 0 < n) (hp : p ≤ n)
    (target : Fin n) :
    (𝔼 sample ∈ occupancySamples n m p,
      targetOccupiedIndicator sample target) =
      1 - (1 - (p : ℝ) / (n : ℝ)) ^ m := by
  rw [show (fun sample => targetOccupiedIndicator sample target) =
      (fun sample => (1 : ℝ) - sampleMissIndicator sample target) by rfl,
    Finset.expect_sub_distrib,
    Finset.expect_const (occupancySamples_nonempty hp),
    sampleMissExpectation hn hp target]

/-- Equation (30), exact equality: expected occupied targets under independent
uniform selection of distinct collateral targets. -/
theorem expectedOccupied_eq_exactFormula {n m p : ℕ} (hn : 0 < n) (hp : p ≤ n) :
    expectedOccupied n m p = exactOccupancyFormula n m p := by
  calc
    expectedOccupied n m p =
        𝔼 sample ∈ occupancySamples n m p,
          ∑ target, targetOccupiedIndicator sample target := by
      unfold expectedOccupied
      apply Finset.expect_congr rfl
      intro sample _hsample
      exact cast_occupiedCount_eq_sum_indicators sample
    _ = ∑ target : Fin n,
          𝔼 sample ∈ occupancySamples n m p,
            targetOccupiedIndicator sample target := by
      exact Finset.expect_sum_comm _ _ _
    _ = ∑ _target : Fin n,
          (1 - (1 - (p : ℝ) / (n : ℝ)) ^ m) := by
      apply Finset.sum_congr rfl
      intro target _htarget
      exact targetOccupiedExpectation hn hp target
    _ = exactOccupancyFormula n m p := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      unfold exactOccupancyFormula
      rw [mul_sub, mul_one]

/-! ## Parameter boundaries -/

/-- Parameters for which the printed real-valued formula denotes a nonempty target
population and each axon can choose `p` distinct targets. -/
def ValidOccupancyParameters (n p : ℕ) : Prop :=
  0 < n ∧ p ≤ n

theorem occupancySamples_eq_empty_of_invalid {n m p : ℕ}
    (hm : 0 < m) (hp : n < p) : occupancySamples n m p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro sample hsample
  let axon : Fin m := ⟨0, hm⟩
  have hchoice := Fintype.mem_piFinset.mp hsample axon
  rw [collateralChoices_eq_empty_iff.mpr hp] at hchoice
  simp at hchoice

theorem expectedOccupied_zero_targets (m p : ℕ) :
    expectedOccupied 0 m p = 0 := by
  simp [expectedOccupied, occupiedCount, occupiedTargets]

theorem expectedOccupied_eq_zero_of_invalid {n m p : ℕ}
    (hm : 0 < m) (hp : n < p) : expectedOccupied n m p = 0 := by
  rw [expectedOccupied, occupancySamples_eq_empty_of_invalid hm hp]
  exact Finset.expect_empty _

theorem expectedOccupied_zero_axons (n p : ℕ) :
    expectedOccupied n 0 p = 0 := by
  simp [expectedOccupied, occupiedCount, occupiedTargets]

theorem expectedOccupied_zero_collaterals (n m : ℕ) :
    expectedOccupied n m 0 = 0 := by
  by_cases hn : n = 0
  · subst n
    exact expectedOccupied_zero_targets m 0
  · rw [expectedOccupied_eq_exactFormula (Nat.pos_of_ne_zero hn) (Nat.zero_le n)]
    simp [exactOccupancyFormula]

/-! ## Approximation boundaries -/

/-- The exponential expression printed after the approximation sign in equation
(30). It is not definitionally identified with the exact finite expectation. -/
def exponentialOccupancyApproximation (n m p : ℕ) : ℝ :=
  (n : ℝ) *
    (1 - Real.exp (-((m : ℝ) * (p : ℝ) / (n : ℝ))))

/-- An explicit error interface for replacing the exact binomial expression by the
exponential expression. -/
def ExponentialOccupancyErrorBound (n m p : ℕ) (δ : ℝ) : Prop :=
  |exactOccupancyFormula n m p - exponentialOccupancyApproximation n m p| ≤ δ

theorem expectedOccupied_exponential_error {n m p : ℕ}
    (hn : 0 < n) (hp : p ≤ n) {δ : ℝ}
    (hApprox : ExponentialOccupancyErrorBound n m p δ) :
    |expectedOccupied n m p - exponentialOccupancyApproximation n m p| ≤ δ := by
  rw [expectedOccupied_eq_exactFormula hn hp]
  exact hApprox

/-- On the unit interval, raising two nonnegative bases to a natural power
amplifies their difference by at most the exponent. -/
private theorem pow_sub_pow_le_nat_mul_sub
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (m : ℕ) :
    b ^ m - a ^ m ≤ (m : ℝ) * (b - a) := by
  have hb0 : 0 ≤ b := ha.trans hab
  have hpow := abs_pow_sub_pow_le b a m
  rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ ha hab m)),
    abs_of_nonneg (sub_nonneg.mpr hab), abs_of_nonneg hb0,
    abs_of_nonneg ha, max_eq_left hab] at hpow
  calc
    b ^ m - a ^ m ≤ (b - a) * (m : ℝ) * b ^ (m - 1) := hpow
    _ ≤ (b - a) * (m : ℝ) * 1 := by
      gcongr
      exact pow_le_one₀ hb0 hb
    _ = (m : ℝ) * (b - a) := by ring

/-- The signed comparison behind equation (30)'s exponential approximation.
The exact expression exceeds the exponential replacement, and their gap is at
most `m p² / n`. -/
private theorem occupancyApproximation_signed_bounds
    {n m p : ℕ} (hn : 0 < n) (hp : p ≤ n) :
    0 ≤ exactOccupancyFormula n m p - exponentialOccupancyApproximation n m p ∧
      exactOccupancyFormula n m p - exponentialOccupancyApproximation n m p ≤
        (m : ℝ) * (p : ℝ) ^ 2 / (n : ℝ) := by
  let x : ℝ := (p : ℝ) / (n : ℝ)
  let a : ℝ := 1 - x
  let b : ℝ := Real.exp (-x)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpR : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hnR).mpr hpR
  have ha0 : 0 ≤ a := by
    dsimp [a]
    linarith
  have hab : a ≤ b := by
    dsimp [a, b]
    exact Real.one_sub_le_exp_neg x
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact (Real.exp_pos _).le
  have hb1 : b ≤ 1 := by
    dsimp [b]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx0)
  have habs : |-x| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hx0]
    exact hx1
  have hlocalAbs : |b - a| ≤ x ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le habs
    dsimp [a, b]
    convert h using 1 <;> ring_nf
  have hlocal : b - a ≤ x ^ 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hlocalAbs
    exact hlocalAbs
  have hpowMono : a ^ m ≤ b ^ m := pow_le_pow_left₀ ha0 hab m
  have hpowError : b ^ m - a ^ m ≤ (m : ℝ) * x ^ 2 := by
    calc
      b ^ m - a ^ m ≤ (m : ℝ) * (b - a) :=
        pow_sub_pow_le_nat_mul_sub ha0 hab hb1 m
      _ ≤ (m : ℝ) * x ^ 2 := by gcongr
  have hexpPower :
      Real.exp (-((m : ℝ) * (p : ℝ) / (n : ℝ))) = b ^ m := by
    rw [show -((m : ℝ) * (p : ℝ) / (n : ℝ)) = (m : ℝ) * (-x) by
      dsimp [x]
      ring]
    exact Real.exp_nat_mul (-x) m
  have hformula :
      exactOccupancyFormula n m p - exponentialOccupancyApproximation n m p =
        (n : ℝ) * (b ^ m - a ^ m) := by
    unfold exactOccupancyFormula exponentialOccupancyApproximation
    rw [hexpPower]
    dsimp [a, x]
    ring
  constructor
  · rw [hformula]
    exact mul_nonneg hnR.le (sub_nonneg.mpr hpowMono)
  · rw [hformula]
    calc
      (n : ℝ) * (b ^ m - a ^ m) ≤ (n : ℝ) * ((m : ℝ) * x ^ 2) :=
        mul_le_mul_of_nonneg_left hpowError hnR.le
      _ = (m : ℝ) * (p : ℝ) ^ 2 / (n : ℝ) := by
        dsimp [x]
        field_simp

/-- Equation (30)'s exponential expression underestimates the exact finite
occupancy expression for valid parameters. -/
theorem exponentialOccupancyApproximation_le_exactOccupancyFormula
    {n m p : ℕ} (hn : 0 < n) (hp : p ≤ n) :
    exponentialOccupancyApproximation n m p ≤ exactOccupancyFormula n m p := by
  exact sub_nonneg.mp (occupancyApproximation_signed_bounds hn hp).1

/-- Explicit signed error bound for equation (30)'s exponential replacement. -/
theorem exactOccupancyFormula_sub_exponentialOccupancyApproximation_le
    {n m p : ℕ} (hn : 0 < n) (hp : p ≤ n) :
    exactOccupancyFormula n m p - exponentialOccupancyApproximation n m p ≤
      (m : ℝ) * (p : ℝ) ^ 2 / (n : ℝ) :=
  (occupancyApproximation_signed_bounds hn hp).2

/-- A constructive witness for the named exponential-approximation error
interface. -/
theorem exponentialOccupancyErrorBound_sq
    {n m p : ℕ} (hn : 0 < n) (hp : p ≤ n) :
    ExponentialOccupancyErrorBound n m p
      ((m : ℝ) * (p : ℝ) ^ 2 / (n : ℝ)) := by
  unfold ExponentialOccupancyErrorBound
  rw [abs_of_nonneg (occupancyApproximation_signed_bounds hn hp).1]
  exact exactOccupancyFormula_sub_exponentialOccupancyApproximation_le hn hp

/-- Equation (30)'s exponential expression also underestimates the exact expected
occupancy of the finite experiment. -/
theorem exponentialOccupancyApproximation_le_expectedOccupied
    {n m p : ℕ} (hn : 0 < n) (hp : p ≤ n) :
    exponentialOccupancyApproximation n m p ≤ expectedOccupied n m p := by
  rw [expectedOccupied_eq_exactFormula hn hp]
  exact exponentialOccupancyApproximation_le_exactOccupancyFormula hn hp

/-- The exact finite expectation is within `m p² / n` of equation (30)'s
exponential approximation. -/
theorem expectedOccupied_exponential_sq_error
    {n m p : ℕ} (hn : 0 < n) (hp : p ≤ n) :
    |expectedOccupied n m p - exponentialOccupancyApproximation n m p| ≤
      (m : ℝ) * (p : ℝ) ^ 2 / (n : ℝ) :=
  expectedOccupied_exponential_error hn hp
    (exponentialOccupancyErrorBound_sq hn hp)

/-- Abstract per-target probabilities for two messages. The joint probabilities are
kept separate so targetwise independence remains a visible premise. -/
structure TwoMessageTargetModel (n : ℕ) where
  firstHitProbability : Fin n → ℝ
  secondHitProbability : Fin n → ℝ
  jointHitProbability : Fin n → ℝ

/-- The additional targetwise independence approximation stated after equation
(30). -/
def TwoMessageTargetModel.TargetwiseIndependent {n : ℕ}
    (M : TwoMessageTargetModel n) : Prop :=
  ∀ target,
    M.jointHitProbability target =
      M.firstHitProbability target * M.secondHitProbability target

/-- Both occupied target sets have the uniform marginal hit probability `q / n`. -/
def TwoMessageTargetModel.HasUniformMarginals {n : ℕ}
    (M : TwoMessageTargetModel n) (q : ℝ) : Prop :=
  ∀ target,
    M.firstHitProbability target = q / (n : ℝ) ∧
      M.secondHitProbability target = q / (n : ℝ)

/-- Expected overlap represented as a sum of joint target-hit probabilities. -/
def TwoMessageTargetModel.expectedOverlap {n : ℕ}
    (M : TwoMessageTargetModel n) : ℝ :=
  ∑ target, M.jointHitProbability target

/-- Under the explicitly additional independence and uniform-marginal premises, the
two-message overlap is exactly `q² / n`; without those premises this theorem makes no
claim. -/
theorem TwoMessageTargetModel.expectedOverlap_eq_sq_div
    {n : ℕ} (M : TwoMessageTargetModel n) (hn : 0 < n) {q : ℝ}
    (hIndependent : M.TargetwiseIndependent)
    (hUniform : M.HasUniformMarginals q) :
    M.expectedOverlap = q ^ 2 / (n : ℝ) := by
  unfold TwoMessageTargetModel.expectedOverlap
  calc
    (∑ target, M.jointHitProbability target) =
        ∑ _target : Fin n, (q / (n : ℝ)) * (q / (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro target _htarget
      rw [hIndependent target, (hUniform target).1, (hUniform target).2]
    _ = q ^ 2 / (n : ℝ) := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [pow_two]

/-! ## Concrete independent two-message experiment -/

/-- Two messages sampled independently from the exact finite occupancy experiment. -/
def twoMessageOccupancySamples (n m p : ℕ) :
    Finset ((Fin m → Finset (Fin n)) × (Fin m → Finset (Fin n))) :=
  occupancySamples n m p ×ˢ occupancySamples n m p

/-- Targets reached by both messages in a joint sample. -/
def occupiedOverlapTargets {n m : ℕ}
    (samples : (Fin m → Finset (Fin n)) × (Fin m → Finset (Fin n))) :
    Finset (Fin n) :=
  occupiedTargets samples.1 ∩ occupiedTargets samples.2

/-- Number of targets reached by both messages in a joint sample. -/
def occupiedOverlapCount {n m : ℕ}
    (samples : (Fin m → Finset (Fin n)) × (Fin m → Finset (Fin n))) : ℕ :=
  (occupiedOverlapTargets samples).card

/-- Exact expected target overlap for two independently sampled messages. -/
def expectedOccupiedOverlap (n m p : ℕ) : ℝ :=
  𝔼 samples ∈ twoMessageOccupancySamples n m p,
    (occupiedOverlapCount samples : ℝ)

/-- An overlap count is the sum of products of the two messages' target-hit
indicators. -/
theorem cast_occupiedOverlapCount_eq_sum_indicators {n m : ℕ}
    (samples : (Fin m → Finset (Fin n)) × (Fin m → Finset (Fin n))) :
    (occupiedOverlapCount samples : ℝ) =
      ∑ target, targetOccupiedIndicator samples.1 target *
        targetOccupiedIndicator samples.2 target := by
  classical
  calc
    (occupiedOverlapCount samples : ℝ) =
        ∑ target ∈ (Finset.univ : Finset (Fin n)),
          if target ∈ occupiedOverlapTargets samples then (1 : ℝ) else 0 := by
      rw [occupiedOverlapCount, Finset.sum_boole]
      congr 2
      ext target
      simp [occupiedOverlapTargets]
    _ = ∑ target, targetOccupiedIndicator samples.1 target *
          targetOccupiedIndicator samples.2 target := by
      apply Finset.sum_congr rfl
      intro target _htarget
      rw [targetOccupiedIndicator_eq, targetOccupiedIndicator_eq]
      by_cases hfirst : target ∈ occupiedTargets samples.1 <;>
        by_cases hsecond : target ∈ occupiedTargets samples.2 <;>
        simp [occupiedOverlapTargets, hfirst, hsecond]

/-- The abstract two-message model induced by the concrete independent product
experiment. -/
def independentOccupancyTargetModel (n m p : ℕ) :
    TwoMessageTargetModel n where
  firstHitProbability := fun target =>
    𝔼 sample ∈ occupancySamples n m p, targetOccupiedIndicator sample target
  secondHitProbability := fun target =>
    𝔼 sample ∈ occupancySamples n m p, targetOccupiedIndicator sample target
  jointHitProbability := fun target =>
    𝔼 samples ∈ twoMessageOccupancySamples n m p,
      targetOccupiedIndicator samples.1 target *
        targetOccupiedIndicator samples.2 target

/-- Cartesian-product sampling constructively supplies the targetwise independence
premise. -/
theorem independentOccupancyTargetModel_targetwiseIndependent (n m p : ℕ) :
    (independentOccupancyTargetModel n m p).TargetwiseIndependent := by
  intro target
  change (𝔼 samples ∈ twoMessageOccupancySamples n m p,
      targetOccupiedIndicator samples.1 target *
        targetOccupiedIndicator samples.2 target) =
    (𝔼 sample ∈ occupancySamples n m p,
      targetOccupiedIndicator sample target) *
    (𝔼 sample ∈ occupancySamples n m p,
      targetOccupiedIndicator sample target)
  rw [twoMessageOccupancySamples, Finset.expect_product]
  change (𝔼 first ∈ occupancySamples n m p,
      𝔼 second ∈ occupancySamples n m p,
        targetOccupiedIndicator first target *
          targetOccupiedIndicator second target) = _
  rw [← Finset.expect_mul_expect]

/-- Each target has marginal hit probability equal to the exact expected occupied
count divided by the target population size. -/
theorem independentOccupancyTargetModel_hasUniformMarginals
    {n m p : ℕ} (hn : 0 < n) (hp : p ≤ n) :
    (independentOccupancyTargetModel n m p).HasUniformMarginals
      (exactOccupancyFormula n m p) := by
  intro target
  change (𝔼 sample ∈ occupancySamples n m p,
      targetOccupiedIndicator sample target) = exactOccupancyFormula n m p / (n : ℝ) ∧
    (𝔼 sample ∈ occupancySamples n m p,
      targetOccupiedIndicator sample target) = exactOccupancyFormula n m p / (n : ℝ)
  rw [targetOccupiedExpectation hn hp]
  constructor <;> unfold exactOccupancyFormula <;> field_simp

/-- The target-model overlap is exactly the expected cardinality of the concrete
intersection experiment. -/
theorem independentOccupancyTargetModel_expectedOverlap_eq
    (n m p : ℕ) :
    (independentOccupancyTargetModel n m p).expectedOverlap =
      expectedOccupiedOverlap n m p := by
  unfold TwoMessageTargetModel.expectedOverlap independentOccupancyTargetModel
  rw [expectedOccupiedOverlap]
  calc
    (∑ target : Fin n,
        𝔼 samples ∈ twoMessageOccupancySamples n m p,
          targetOccupiedIndicator samples.1 target *
            targetOccupiedIndicator samples.2 target) =
        𝔼 samples ∈ twoMessageOccupancySamples n m p,
          ∑ target, targetOccupiedIndicator samples.1 target *
            targetOccupiedIndicator samples.2 target := by
      exact (Finset.expect_sum_comm _ _ _).symm
    _ = 𝔼 samples ∈ twoMessageOccupancySamples n m p,
          (occupiedOverlapCount samples : ℝ) := by
      apply Finset.expect_congr rfl
      intro samples _hsamples
      exact (cast_occupiedOverlapCount_eq_sum_indicators samples).symm

/-- Under literal independent product sampling, the expected overlap following
equation (30) is exactly `q²/n`, with `q` equal to the exact one-message expected
occupancy. -/
theorem expectedOccupiedOverlap_eq_sq_div
    {n m p : ℕ} (hn : 0 < n) (hp : p ≤ n) :
    expectedOccupiedOverlap n m p =
      exactOccupancyFormula n m p ^ 2 / (n : ℝ) := by
  rw [← independentOccupancyTargetModel_expectedOverlap_eq]
  exact TwoMessageTargetModel.expectedOverlap_eq_sq_div
    (independentOccupancyTargetModel n m p) hn
    (independentOccupancyTargetModel_targetwiseIndependent n m p)
    (independentOccupancyTargetModel_hasUniformMarginals hn hp)

/-! ### Two-message parameter boundaries -/

theorem twoMessageOccupancySamples_eq_empty_of_invalid
    {n m p : ℕ} (hm : 0 < m) (hp : n < p) :
    twoMessageOccupancySamples n m p = ∅ := by
  rw [twoMessageOccupancySamples, occupancySamples_eq_empty_of_invalid hm hp]
  simp

theorem expectedOccupiedOverlap_eq_zero_of_invalid
    {n m p : ℕ} (hm : 0 < m) (hp : n < p) :
    expectedOccupiedOverlap n m p = 0 := by
  rw [expectedOccupiedOverlap,
    twoMessageOccupancySamples_eq_empty_of_invalid hm hp]
  exact Finset.expect_empty _

theorem expectedOccupiedOverlap_zero_targets (m p : ℕ) :
    expectedOccupiedOverlap 0 m p = 0 := by
  simp [expectedOccupiedOverlap, twoMessageOccupancySamples,
    occupiedOverlapCount, occupiedOverlapTargets, occupiedTargets]

theorem expectedOccupiedOverlap_zero_axons (n p : ℕ) :
    expectedOccupiedOverlap n 0 p = 0 := by
  simp [expectedOccupiedOverlap, twoMessageOccupancySamples,
    occupiedOverlapCount, occupiedOverlapTargets, occupiedTargets]

theorem expectedOccupiedOverlap_zero_collaterals (n m : ℕ) :
    expectedOccupiedOverlap n m 0 = 0 := by
  by_cases hn : n = 0
  · subst n
    exact expectedOccupiedOverlap_zero_targets m 0
  · rw [expectedOccupiedOverlap_eq_sq_div
      (Nat.pos_of_ne_zero hn) (Nat.zero_le n)]
    simp [exactOccupancyFormula]

end

end IPNPCNS
