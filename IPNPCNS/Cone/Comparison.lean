import IPNPCNS.Cone.Laws
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Directional comparison of closed cones

This module formalizes equations (87)--(92).  The exact infima and finite minima are
given total Lean definitions, but every theorem assigning them the paper's semantics
requires nonzero cones and nonempty finite frames explicitly.
-/

open Set

namespace IPNPCNS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Metric projection onto a closed convex cone is nonexpansive. -/
theorem metricProjection_nonexpansive (C : ClosedCone H) (x y : H) :
    ‖metricProjection C x - metricProjection C y‖ ≤ ‖x - y‖ := by
  let px := metricProjection C x
  let py := metricProjection C y
  have hxy := metricProjection_inner_le_zero C x py (metricProjection_mem C y)
  have hyx := metricProjection_inner_le_zero C y px (metricProjection_mem C x)
  have hxy' : 0 ≤ inner ℝ (x - px) (px - py) := by
    rw [show py - px = -(px - py) by abel, inner_neg_right] at hxy
    linarith
  have hdiff :
      0 ≤ inner ℝ ((x - px) - (y - py)) (px - py) := by
    rw [inner_sub_left]
    linarith
  have hfirm :
      ‖px - py‖ ^ 2 ≤ inner ℝ (x - y) (px - py) := by
    have hrearrange : (x - px) - (y - py) = (x - y) - (px - py) := by
      abel
    rw [hrearrange, inner_sub_left, real_inner_self_eq_norm_sq] at hdiff
    linarith
  have hcs := real_inner_le_norm (x - y) (px - py)
  change ‖px - py‖ ≤ ‖x - y‖
  by_cases hzero : ‖px - py‖ = 0
  · rw [hzero]
    exact norm_nonneg _
  · have hpos : 0 < ‖px - py‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith

/-- Projection cannot increase the norm. -/
theorem norm_metricProjection_le (C : ClosedCone H) (x : H) :
    ‖metricProjection C x‖ ≤ ‖x‖ := by
  have h := metricProjection_nonexpansive C x 0
  have hzero : metricProjection C 0 = 0 := metricProjection_eq_self C.zero_mem
  simpa [hzero] using h

/-- The projection norm is a one-Lipschitz scalar function. -/
theorem projectionNorm_lipschitz (C : ClosedCone H) (x y : H) :
    ‖metricProjection C x‖ - ‖metricProjection C y‖ ≤ ‖x - y‖ := by
  exact (norm_sub_norm_le _ _).trans (metricProjection_nonexpansive C x y)

/-- Equation (87), restricted to directions contained in a cone. -/
def unitDirections (C : ClosedCone H) : Set H :=
  {x | x ∈ C ∧ ‖x‖ = 1}

/-- Normalize a nonzero ray representative, as in equation (90). -/
def normalizeRay (x : H) : H :=
  ‖x‖⁻¹ • x

omit [CompleteSpace H] in
theorem normalizeRay_mem {C : ClosedCone H} {x : H} (hx : x ∈ C) :
    normalizeRay x ∈ C := by
  exact C.smul_mem hx (inv_nonneg.mpr (norm_nonneg x))

omit [CompleteSpace H] in
theorem norm_normalizeRay {x : H} (hx : x ≠ 0) :
    ‖normalizeRay x‖ = 1 := by
  simp [normalizeRay, norm_smul, norm_inv, norm_ne_zero_iff.mpr hx]

omit [CompleteSpace H] in
theorem exists_nonzero_mem_of_ne_bot {C : ClosedCone H} (hC : C ≠ ⊥) :
    ∃ x ∈ C, x ≠ 0 := by
  by_contra h
  apply hC
  ext x
  constructor
  · intro hx
    rw [ProperCone.mem_bot]
    by_contra hx0
    exact h ⟨x, hx, hx0⟩
  · intro hx
    rw [ProperCone.mem_bot] at hx
    subst x
    exact C.zero_mem

omit [CompleteSpace H] in
theorem unitDirections_nonempty {C : ClosedCone H} (hC : C ≠ ⊥) :
    (unitDirections C).Nonempty := by
  rcases exists_nonzero_mem_of_ne_bot hC with ⟨x, hxC, hx0⟩
  exact ⟨normalizeRay x, normalizeRay_mem hxC, norm_normalizeRay hx0⟩

/-- The set whose infimum is the directed term in equation (88). -/
def projectionNormSet (A B : ClosedCone H) : Set ℝ :=
  (fun x => ‖metricProjection B x‖) '' unitDirections A

theorem projectionNormSet_bddBelow (A B : ClosedCone H) :
    BddBelow (projectionNormSet A B) := by
  refine ⟨0, ?_⟩
  rintro z ⟨x, _hx, rfl⟩
  exact norm_nonneg _

theorem projectionNormSet_nonempty {A B : ClosedCone H} (hA : A ≠ ⊥) :
    (projectionNormSet A B).Nonempty :=
  (unitDirections_nonempty hA).image _

/-- One directed infimum in equation (88): source directions are tested against the
target cone. -/
def directionalConeSimilarity (A B : ClosedCone H) : ℝ :=
  sInf (projectionNormSet A B)

/-- Equation (88): symmetric worst-case cone similarity. -/
def coneSimilarity (A B : ClosedCone H) : ℝ :=
  min (directionalConeSimilarity A B) (directionalConeSimilarity B A)

/-- Equation (89): angular cone mismatch. -/
def coneAngle (A B : ClosedCone H) : ℝ :=
  Real.arccos (coneSimilarity A B)

theorem coneSimilarity_comm (A B : ClosedCone H) :
    coneSimilarity A B = coneSimilarity B A := by
  simp [coneSimilarity, min_comm]

theorem coneAngle_comm (A B : ClosedCone H) :
    coneAngle A B = coneAngle B A := by
  rw [coneAngle, coneAngle, coneSimilarity_comm]

/-- The inclusion test stated before equation (87): rejection is empty exactly when
the source cone is included in the target cone. -/
theorem coneRejection_eq_bot_iff_le (A B : ClosedCone H) :
    coneRejection A B = ⊥ ↔ A ≤ B := by
  constructor
  · intro hEmpty x hxA
    have hzero : metricProjection (polar B) x = 0 := by
      have hmem := metricProjection_polar_mem_coneRejection A B hxA
      rw [hEmpty, ProperCone.mem_bot] at hmem
      exact hmem
    rw [moreau_add B x, hzero, add_zero]
    exact metricProjection_mem B x
  · intro hAB
    apply le_antisymm
    · change conicHull (projectedSet A (polar B)) ≤ ⊥
      apply conicHull_le
      rintro y ⟨x, hxA, rfl⟩
      change metricProjection (polar B) x = 0
      rw [metricProjection_polar_eq_sub,
        metricProjection_eq_self (hAB hxA), sub_self]
    · exact bot_le

theorem cone_eq_iff_mutual_rejection_bot (A B : ClosedCone H) :
    A = B ↔ coneRejection A B = ⊥ ∧ coneRejection B A = ⊥ := by
  rw [coneRejection_eq_bot_iff_le, coneRejection_eq_bot_iff_le]
  exact le_antisymm_iff

theorem directionalConeSimilarity_nonneg {A B : ClosedCone H} (hA : A ≠ ⊥) :
    0 ≤ directionalConeSimilarity A B := by
  apply le_csInf (projectionNormSet_nonempty hA)
  rintro z ⟨x, _hx, rfl⟩
  exact norm_nonneg _

theorem directionalConeSimilarity_le_one {A B : ClosedCone H} (hA : A ≠ ⊥) :
    directionalConeSimilarity A B ≤ 1 := by
  rcases unitDirections_nonempty hA with ⟨x, hxA⟩
  refine (csInf_le (projectionNormSet_bddBelow A B) ⟨x, hxA, rfl⟩).trans ?_
  exact (norm_metricProjection_le B x).trans_eq hxA.2

/-- The range assertion following equation (89). -/
theorem coneSimilarity_mem_unitInterval {A B : ClosedCone H}
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) :
    coneSimilarity A B ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_min (directionalConeSimilarity_nonneg hA)
      (directionalConeSimilarity_nonneg hB)
  · exact (min_le_left _ _).trans (directionalConeSimilarity_le_one hA)

theorem directionalConeSimilarity_self {A : ClosedCone H} (hA : A ≠ ⊥) :
    directionalConeSimilarity A A = 1 := by
  apply le_antisymm (directionalConeSimilarity_le_one hA)
  apply le_csInf (projectionNormSet_nonempty hA)
  rintro z ⟨x, hx, rfl⟩
  change 1 ≤ ‖metricProjection A x‖
  rw [metricProjection_eq_self hx.1, hx.2]

/-- Identical nonzero cones have similarity one. -/
theorem coneSimilarity_self {A : ClosedCone H} (hA : A ≠ ⊥) :
    coneSimilarity A A = 1 := by
  simp [coneSimilarity, directionalConeSimilarity_self hA]

/-- A point in the polar cone projects to zero. -/
theorem metricProjection_eq_zero_of_mem_polar {C : ClosedCone H} {x : H}
    (hx : x ∈ polar C) : metricProjection C x = 0 := by
  apply metricProjection_eq_of_mem_of_inner_le_zero C x 0 C.zero_mem
  intro z hz
  simpa using (mem_polar.mp hx) z hz

theorem directionalConeSimilarity_eq_zero_of_polar_direction
    {A B : ClosedCone H} (hA : A ≠ ⊥)
    {x : H} (hxA : x ∈ unitDirections A) (hxPolar : x ∈ polar B) :
    directionalConeSimilarity A B = 0 := by
  apply le_antisymm
  · have hmem : (0 : ℝ) ∈ projectionNormSet A B := by
      refine ⟨x, hxA, ?_⟩
      change ‖metricProjection B x‖ = 0
      rw [metricProjection_eq_zero_of_mem_polar hxPolar, norm_zero]
    exact csInf_le (projectionNormSet_bddBelow A B) hmem
  · exact directionalConeSimilarity_nonneg hA

/-- The similarity is zero if either nonzero cone contains a unit direction in the
polar of the other. -/
theorem coneSimilarity_eq_zero_of_polar_direction
    {A B : ClosedCone H} (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hPolar :
      (∃ x ∈ unitDirections A, x ∈ polar B) ∨
        (∃ y ∈ unitDirections B, y ∈ polar A)) :
    coneSimilarity A B = 0 := by
  rcases hPolar with ⟨x, hxA, hxPolar⟩ | ⟨y, hyB, hyPolar⟩
  · rw [coneSimilarity,
      directionalConeSimilarity_eq_zero_of_polar_direction hA hxA hxPolar]
    exact min_eq_left (directionalConeSimilarity_nonneg hB)
  · rw [coneSimilarity,
      directionalConeSimilarity_eq_zero_of_polar_direction hB hyB hyPolar]
    exact min_eq_right (directionalConeSimilarity_nonneg hA)

/-- Equation (89) lies between zero and a right angle. -/
theorem coneAngle_mem_halfPi {A B : ClosedCone H}
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) :
    coneAngle A B ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  refine ⟨Real.arccos_nonneg _, ?_⟩
  unfold coneAngle
  rw [Real.arccos_le_pi_div_two]
  exact (coneSimilarity_mem_unitInterval hA hB).1

theorem coneAngle_self {A : ClosedCone H} (hA : A ≠ ⊥) :
    coneAngle A A = 0 := by
  simp [coneAngle, coneSimilarity_self hA]

theorem coneAngle_eq_halfPi_of_polar_direction
    {A B : ClosedCone H} (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hPolar :
      (∃ x ∈ unitDirections A, x ∈ polar B) ∨
        (∃ y ∈ unitDirections B, y ∈ polar A)) :
    coneAngle A B = Real.pi / 2 := by
  rw [coneAngle, coneSimilarity_eq_zero_of_polar_direction hA hB hPolar,
    Real.arccos_zero]

/-! ## Finite normalized-frame proxy -/

/-- A finite frame before normalization. Every indexed vector is a nonzero member of
the represented cone. Finiteness and nonemptiness of the index type are required by
the proxy definitions below. -/
structure ConeFrame (C : ClosedCone H) (ι : Type*) where
  vector : ι → H
  mem_cone : ∀ i, vector i ∈ C
  nonzero : ∀ i, vector i ≠ 0

namespace ConeFrame

variable {C : ClosedCone H} {ι : Type*}

/-- Equation (90): the normalized ray indexed by a frame. -/
def normalized (F : ConeFrame C ι) (i : ι) : H :=
  normalizeRay (F.vector i)

omit [CompleteSpace H] in
theorem normalized_mem (F : ConeFrame C ι) (i : ι) :
    F.normalized i ∈ C :=
  normalizeRay_mem (F.mem_cone i)

omit [CompleteSpace H] in
theorem norm_normalized (F : ConeFrame C ι) (i : ι) :
    ‖F.normalized i‖ = 1 :=
  norm_normalizeRay (F.nonzero i)

omit [CompleteSpace H] in
theorem normalized_mem_unitDirections (F : ConeFrame C ι) (i : ι) :
    F.normalized i ∈ unitDirections C :=
  ⟨F.normalized_mem i, F.norm_normalized i⟩

end ConeFrame

variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]

/-- One finite minimum in equation (91). -/
def frameDirectionalSimilarity {A : ClosedCone H}
    (B : ClosedCone H) (F : ConeFrame A ι) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun i => ‖metricProjection B (F.normalized i)‖)

/-- Equation (91): the symmetric finite normalized-frame proxy. -/
def frameConeSimilarity (A B : ClosedCone H)
    (FA : ConeFrame A ι) (FB : ConeFrame B κ) : ℝ :=
  min (frameDirectionalSimilarity B FA) (frameDirectionalSimilarity A FB)

theorem frameConeSimilarity_comm
    (A B : ClosedCone H) (FA : ConeFrame A ι) (FB : ConeFrame B κ) :
    frameConeSimilarity A B FA FB = frameConeSimilarity B A FB FA := by
  simp [frameConeSimilarity, min_comm]

/-- Every source unit direction is within `γ` of some normalized frame ray. -/
def FrameCoverage {C : ClosedCone H} (F : ConeFrame C ι) (γ : ℝ) : Prop :=
  ∀ x ∈ unitDirections C, ∃ i, ‖x - F.normalized i‖ ≤ γ

theorem frameDirectionalSimilarity_nonneg {A B : ClosedCone H}
    (F : ConeFrame A ι) :
    0 ≤ frameDirectionalSimilarity B F := by
  rw [frameDirectionalSimilarity, Finset.le_inf'_iff]
  intro i _hi
  exact norm_nonneg _

theorem frameDirectionalSimilarity_le_one {A B : ClosedCone H}
    (F : ConeFrame A ι) :
    frameDirectionalSimilarity B F ≤ 1 := by
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  refine (Finset.inf'_le _ (Finset.mem_univ i)).trans ?_
  exact (norm_metricProjection_le B (F.normalized i)).trans_eq
    (F.norm_normalized i)

theorem frameConeSimilarity_mem_unitInterval
    (A B : ClosedCone H) (FA : ConeFrame A ι) (FB : ConeFrame B κ) :
    frameConeSimilarity A B FA FB ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_min (frameDirectionalSimilarity_nonneg FA)
      (frameDirectionalSimilarity_nonneg FB)
  · exact (min_le_left _ _).trans (frameDirectionalSimilarity_le_one FA)

/-- The exact directed infimum is no larger than the finite-frame minimum. -/
theorem directionalConeSimilarity_le_frame
    {A B : ClosedCone H} (_hA : A ≠ ⊥) (F : ConeFrame A ι) :
    directionalConeSimilarity A B ≤ frameDirectionalSimilarity B F := by
  rw [frameDirectionalSimilarity, Finset.le_inf'_iff]
  intro i _hi
  apply csInf_le (projectionNormSet_bddBelow A B)
  exact ⟨F.normalized i, F.normalized_mem_unitDirections i, rfl⟩

/-- The finite proxy in (91) is optimistic even without a coverage assumption. -/
theorem coneSimilarity_le_frameConeSimilarity
    {A B : ClosedCone H} (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (FA : ConeFrame A ι) (FB : ConeFrame B κ) :
    coneSimilarity A B ≤ frameConeSimilarity A B FA FB := by
  exact min_le_min (directionalConeSimilarity_le_frame hA FA)
    (directionalConeSimilarity_le_frame hB FB)

/-- Coverage and projection nonexpansiveness put a finite directed minimum within
`γ` above its exact infimum. -/
theorem frameDirectionalSimilarity_le_add
    {A B : ClosedCone H} (hA : A ≠ ⊥) (F : ConeFrame A ι) {γ : ℝ}
    (hCoverage : FrameCoverage F γ) :
    frameDirectionalSimilarity B F ≤ directionalConeSimilarity A B + γ := by
  have hlower :
      frameDirectionalSimilarity B F - γ ≤ directionalConeSimilarity A B := by
    apply le_csInf (projectionNormSet_nonempty hA)
    rintro z ⟨x, hx, rfl⟩
    rcases hCoverage x hx with ⟨i, hi⟩
    have hmin : frameDirectionalSimilarity B F ≤
        ‖metricProjection B (F.normalized i)‖ :=
      Finset.inf'_le _ (Finset.mem_univ i)
    have hlip := projectionNorm_lipschitz B (F.normalized i) x
    have hdist : ‖F.normalized i - x‖ ≤ γ := by
      simpa [norm_sub_rev] using hi
    change frameDirectionalSimilarity B F - γ ≤ ‖metricProjection B x‖
    linarith
  linarith

theorem directionalFrame_error
    {A B : ClosedCone H} (hA : A ≠ ⊥) (F : ConeFrame A ι) {γ : ℝ}
    (_hγ : 0 ≤ γ) (hCoverage : FrameCoverage F γ) :
    0 ≤ frameDirectionalSimilarity B F - directionalConeSimilarity A B ∧
      frameDirectionalSimilarity B F - directionalConeSimilarity A B ≤ γ := by
  constructor
  · exact sub_nonneg.mpr (directionalConeSimilarity_le_frame hA F)
  · apply sub_le_iff_le_add.mpr
    simpa only [add_comm] using
      (frameDirectionalSimilarity_le_add (A := A) (B := B) hA F hCoverage)

/-- Equation (92): two-sided directional coverage controls the optimistic symmetric
finite-frame proxy. -/
theorem frameConeSimilarity_error92
    {A B : ClosedCone H} (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (FA : ConeFrame A ι) (FB : ConeFrame B κ) {γ : ℝ}
    (_hγ : 0 ≤ γ) (hCoverA : FrameCoverage FA γ)
    (hCoverB : FrameCoverage FB γ) :
    0 ≤ frameConeSimilarity A B FA FB - coneSimilarity A B ∧
      frameConeSimilarity A B FA FB - coneSimilarity A B ≤ γ := by
  constructor
  · exact sub_nonneg.mpr (coneSimilarity_le_frameConeSimilarity hA hB FA FB)
  · apply sub_le_iff_le_add.mpr
    have hdirA := frameDirectionalSimilarity_le_add
      (A := A) (B := B) hA FA hCoverA
    have hdirB := frameDirectionalSimilarity_le_add
      (A := B) (B := A) hB FB hCoverB
    unfold frameConeSimilarity coneSimilarity
    have hmin := min_le_min hdirA hdirB
    rw [min_add_add_right] at hmin
    linarith

end

end IPNPCNS
