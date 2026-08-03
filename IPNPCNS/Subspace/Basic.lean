import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Finite-dimensional real subspace algebra

This module gives coordinate-free meanings to the five subspace operations in
Section 2.3.  Matrix formulas are representation theorems for these intrinsic
objects and are developed separately.
-/

namespace IPNPCNS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

/-- The projection of every vector in `P` onto `Q`, corresponding to `p ⌞ q`. -/
def subspaceProjection (P Q : Submodule ℝ H) : Submodule ℝ H :=
  P.map Q.starProjection.toLinearMap

/-- The rejection of `Q` from `P`, corresponding to `p ¬ q`. -/
def subspaceRejection (P Q : Submodule ℝ H) : Submodule ℝ H :=
  subspaceProjection P Qᗮ

/-- Equation (12), intrinsically: the complementary projector is `I - P`. -/
theorem complement_starProjection (P : Submodule ℝ H) :
    Pᗮ.starProjection = 1 - P.starProjection :=
  Submodule.starProjection_orthogonal' P

/-- Equation (15): projecting a subspace is the range of the composed projectors. -/
theorem subspaceProjection_eq_range_comp (P Q : Submodule ℝ H) :
    subspaceProjection P Q =
      (Q.starProjection.toLinearMap.comp P.starProjection.toLinearMap).range := by
  apply le_antisymm
  · rintro z ⟨x, hx, rfl⟩
    refine ⟨x, ?_⟩
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [Submodule.starProjection_eq_self_iff.mpr hx]
  · rintro z ⟨x, rfl⟩
    refine ⟨P.starProjection x, P.starProjection_apply_mem x, ?_⟩
    rfl

/-- Equation (16): rejection is projection onto the orthogonal complement. -/
theorem subspaceRejection_eq_range_comp (P Q : Submodule ℝ H) :
    subspaceRejection P Q =
      (Qᗮ.starProjection.toLinearMap.comp P.starProjection.toLinearMap).range :=
  subspaceProjection_eq_range_comp P Qᗮ

omit [FiniteDimensional ℝ H] in
/-- Equation (21): the complement of a sum is the intersection of complements. -/
theorem orthogonal_sup_eq_inf_orthogonal (P Q : Submodule ℝ H) :
    (P ⊔ Q)ᗮ = Pᗮ ⊓ Qᗮ :=
  (Submodule.inf_orthogonal P Q).symm

/-- Equation (22): intersection can be expressed using complements and sum. -/
theorem inf_eq_orthogonal_sup_orthogonal (P Q : Submodule ℝ H) :
    P ⊓ Q = (Pᗮ ⊔ Qᗮ)ᗮ := by
  rw [← Submodule.inf_orthogonal, Submodule.orthogonal_orthogonal,
    Submodule.orthogonal_orthogonal]

/-- Subspace inclusion is exactly emptiness of the orthogonal rejection. -/
theorem le_iff_subspaceRejection_eq_bot (P Q : Submodule ℝ H) :
    P ≤ Q ↔ subspaceRejection P Q = ⊥ := by
  constructor
  · intro hPQ
    apply le_antisymm
    · rintro z ⟨x, hx, rfl⟩
      have hxQ : x ∈ Q := hPQ hx
      have hz : Qᗮ.starProjection x = 0 := by
        rw [Submodule.starProjection_apply_eq_zero_iff]
        simpa using hxQ
      simp [hz]
    · exact bot_le
  · intro hzero x hx
    have hzmem : Qᗮ.starProjection x ∈ subspaceRejection P Q :=
      ⟨x, hx, rfl⟩
    rw [hzero] at hzmem
    have hz : Qᗮ.starProjection x = 0 := hzmem
    rw [Submodule.starProjection_apply_eq_zero_iff] at hz
    simpa using hz

private theorem subspaceRejection_le_orthogonal (P Q : Submodule ℝ H) :
    subspaceRejection P Q ≤ Qᗮ := by
  rintro z ⟨x, -, rfl⟩
  exact Qᗮ.starProjection_apply_mem x

private theorem doubleRejection_pointwise (P Q : Submodule ℝ H) {x : H}
    (hx : x ∈ P) :
    (subspaceRejection P Q)ᗮ.starProjection x = Q.starProjection x := by
  let R := subspaceRejection P Q
  have hq : Q.starProjection x ∈ Rᗮ := by
    rw [Submodule.mem_orthogonal']
    intro r hr
    have hrQ : r ∈ Qᗮ := subspaceRejection_le_orthogonal P Q hr
    exact hrQ _ (Q.starProjection_apply_mem x)
  have hres : x - Q.starProjection x ∈ R := by
    rw [← Q.starProjection_orthogonal_val x]
    exact ⟨x, hx, rfl⟩
  apply Submodule.eq_starProjection_of_mem_orthogonal hq
  simpa [R] using hres

/-- Equations (17)--(20): rejecting the rejection recovers the projection. -/
theorem double_subspaceRejection_eq_projection (P Q : Submodule ℝ H) :
    subspaceRejection P (subspaceRejection P Q) = subspaceProjection P Q := by
  apply le_antisymm
  · rintro z ⟨x, hx, rfl⟩
    exact ⟨x, hx, (doubleRejection_pointwise P Q hx).symm⟩
  · rintro z ⟨x, hx, rfl⟩
    exact ⟨x, hx, doubleRejection_pointwise P Q hx⟩

/-- The sum of the two directed rejection spaces in equation (23). -/
def mutualRejectionSum (P Q : Submodule ℝ H) : Submodule ℝ H :=
  subspaceRejection Q P ⊔ subspaceRejection P Q

private theorem mutualRejectionSum_le_sup (P Q : Submodule ℝ H) :
    mutualRejectionSum P Q ≤ P ⊔ Q := by
  apply sup_le
  · rintro z ⟨x, hx, rfl⟩
    have hmem : x - P.starProjection x ∈ P ⊔ Q :=
      (P ⊔ Q).sub_mem ((le_sup_right : Q ≤ P ⊔ Q) hx)
        ((le_sup_left : P ≤ P ⊔ Q) (P.starProjection_apply_mem x))
    rw [← P.starProjection_orthogonal_val x] at hmem
    exact hmem
  · rintro z ⟨x, hx, rfl⟩
    have hmem : x - Q.starProjection x ∈ P ⊔ Q :=
      (P ⊔ Q).sub_mem ((le_sup_left : P ≤ P ⊔ Q) hx)
        ((le_sup_right : Q ≤ P ⊔ Q) (Q.starProjection_apply_mem x))
    rw [← Q.starProjection_orthogonal_val x] at hmem
    exact hmem

private theorem projection_mem_mutualRejectionSum_left (P Q : Submodule ℝ H)
    {x : H} (hx : x ∈ P ⊔ Q) :
    Qᗮ.starProjection x ∈ mutualRejectionSum P Q := by
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  have hqzero : Qᗮ.starProjection q = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    simpa using hq
  rw [hqzero, add_zero]
  exact (le_sup_right : subspaceRejection P Q ≤ mutualRejectionSum P Q) ⟨p, hp, rfl⟩

private theorem projection_mem_mutualRejectionSum_right (P Q : Submodule ℝ H)
    {x : H} (hx : x ∈ P ⊔ Q) :
    Pᗮ.starProjection x ∈ mutualRejectionSum P Q := by
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  have hpzero : Pᗮ.starProjection p = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    simpa using hp
  rw [hpzero, zero_add]
  exact (le_sup_left : subspaceRejection Q P ≤ mutualRejectionSum P Q) ⟨q, hq, rfl⟩

private theorem mem_inf_of_mem_sup_mem_mutualRejectionSum_orthogonal
    (P Q : Submodule ℝ H) {x : H} (hx : x ∈ P ⊔ Q)
    (horth : x ∈ (mutualRejectionSum P Q)ᗮ) : x ∈ P ⊓ Q := by
  have hxQproj : Qᗮ.starProjection x ∈ mutualRejectionSum P Q :=
    projection_mem_mutualRejectionSum_left P Q hx
  have hinnerQ : inner ℝ x (Qᗮ.starProjection x) = 0 := by
    rw [real_inner_comm]
    exact horth _ hxQproj
  have hnormQ : ‖Qᗮ.starProjection x‖ ^ 2 = 0 := by
    calc
      ‖Qᗮ.starProjection x‖ ^ 2 = inner ℝ (Qᗮ.starProjection x) x := by
        simpa using (Submodule.re_inner_starProjection_eq_normSq Qᗮ x).symm
      _ = 0 := by simpa [real_inner_comm] using hinnerQ
  have hzeroQ : Qᗮ.starProjection x = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormQ)
  have hxQ : x ∈ Q := by
    rw [Submodule.starProjection_apply_eq_zero_iff] at hzeroQ
    simpa using hzeroQ
  have hxPproj : Pᗮ.starProjection x ∈ mutualRejectionSum P Q :=
    projection_mem_mutualRejectionSum_right P Q hx
  have hinnerP : inner ℝ x (Pᗮ.starProjection x) = 0 := by
    rw [real_inner_comm]
    exact horth _ hxPproj
  have hnormP : ‖Pᗮ.starProjection x‖ ^ 2 = 0 := by
    calc
      ‖Pᗮ.starProjection x‖ ^ 2 = inner ℝ (Pᗮ.starProjection x) x := by
        simpa using (Submodule.re_inner_starProjection_eq_normSq Pᗮ x).symm
      _ = 0 := by simpa [real_inner_comm] using hinnerP
  have hzeroP : Pᗮ.starProjection x = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormP)
  have hxP : x ∈ P := by
    rw [Submodule.starProjection_apply_eq_zero_iff] at hzeroP
    simpa using hzeroP
  exact ⟨hxP, hxQ⟩

/-- Equation (23): intersection expressed using sum and directed rejections. -/
theorem intersection_eq_sum_reject_mutualRejections (P Q : Submodule ℝ H) :
    P ⊓ Q = subspaceRejection (P ⊔ Q) (mutualRejectionSum P Q) := by
  let S := mutualRejectionSum P Q
  apply le_antisymm
  · intro x hx
    have hxSup : x ∈ P ⊔ Q :=
      (le_sup_left : P ≤ P ⊔ Q) ((inf_le_left : P ⊓ Q ≤ P) hx)
    have hxOrth : x ∈ Sᗮ := by
      rw [Submodule.mem_orthogonal']
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
      have ha0 : inner ℝ x a = 0 := by
        exact subspaceRejection_le_orthogonal Q P ha x hx.1
      have hb0 : inner ℝ x b = 0 := by
        exact subspaceRejection_le_orthogonal P Q hb x hx.2
      rw [inner_add_right, ha0, hb0, add_zero]
    refine ⟨x, hxSup, ?_⟩
    exact Submodule.starProjection_eq_self_iff.mpr hxOrth
  · rintro z ⟨x, hx, rfl⟩
    have hzOrth : Sᗮ.starProjection x ∈ Sᗮ := Sᗮ.starProjection_apply_mem x
    have hzSup : Sᗮ.starProjection x ∈ P ⊔ Q := by
      rw [S.starProjection_orthogonal_val]
      exact (P ⊔ Q).sub_mem hx
        (mutualRejectionSum_le_sup P Q (S.starProjection_apply_mem x))
    exact mem_inf_of_mem_sup_mem_mutualRejectionSum_orthogonal P Q hzSup hzOrth

end

end IPNPCNS
