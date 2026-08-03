import IPNPCNS.Subspace.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.PID

/-!
# Finite-dimensional subspace comparisons

This module formalizes the trace, orthonormal-basis average, and symmetric
Frobenius comparisons in equations (24) and (27)--(29).  Gleason's theorem is
motivation in the paper, not a premise of any result here.
-/

namespace IPNPCNS

noncomputable section

open scoped Matrix

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

/-- Equation (24): the entrywise Frobenius inner product. -/
def frobeniusInner {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- Equation (24): entrywise Frobenius pairing equals a matrix trace. -/
theorem frobeniusInner_eq_trace_transpose_mul
    {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) :
    frobeniusInner A B = Matrix.trace (A.transpose * B) := by
  classical
  simp only [frobeniusInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- The orthogonal projector represented in an arbitrary orthonormal basis. -/
def subspaceProjectorMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ H) (P : Submodule ℝ H) : Matrix ι ι ℝ :=
  LinearMap.toMatrix b.toBasis b.toBasis P.starProjection.toLinearMap

/-- Orthogonal projector matrices are symmetric. -/
theorem subspaceProjectorMatrix_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ H) (P : Submodule ℝ H) :
    (subspaceProjectorMatrix b P).transpose = subspaceProjectorMatrix b P := by
  classical
  have hadjoint : P.starProjection.toLinearMap.adjoint = P.starProjection.toLinearMap :=
    P.starProjection_isSymmetric.adjoint_eq
  have hmatrix := LinearMap.toMatrix_adjoint b b P.starProjection.toLinearMap
  simpa [subspaceProjectorMatrix, hadjoint] using hmatrix.symm

/-- Equation (12) in any orthonormal coordinate system. -/
theorem subspaceProjectorMatrix_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ H) (P : Submodule ℝ H) :
    subspaceProjectorMatrix b Pᗮ = 1 - subspaceProjectorMatrix b P := by
  unfold subspaceProjectorMatrix
  rw [complement_starProjection]
  simp

/-- The basis-independent unnormalized overlap `tr(PQ)` from equation (27). -/
def subspaceOverlap (P Q : Submodule ℝ H) : ℝ :=
  LinearMap.trace ℝ H
    (P.starProjection.toLinearMap * Q.starProjection.toLinearMap)

/-- Cyclicity of trace makes unnormalized subspace overlap symmetric. -/
theorem subspaceOverlap_comm (P Q : Submodule ℝ H) :
    subspaceOverlap P Q = subspaceOverlap Q P := by
  exact LinearMap.trace_mul_comm ℝ _ _

/-- Equations (24) and (27): overlap is the Frobenius pairing of projector matrices. -/
theorem subspaceOverlap_eq_frobeniusInner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ H) (P Q : Submodule ℝ H) :
    subspaceOverlap P Q =
      frobeniusInner (subspaceProjectorMatrix b P) (subspaceProjectorMatrix b Q) := by
  classical
  rw [frobeniusInner_eq_trace_transpose_mul, subspaceProjectorMatrix_transpose]
  unfold subspaceOverlap subspaceProjectorMatrix
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis,
    LinearMap.toMatrix_mul]

private theorem restrictedOverlap_inner_eq_norm_sq
    (P Q : Submodule ℝ H) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ Q) (i : ι) :
    inner ℝ (b i : H)
        (Q.starProjection (P.starProjection (b i : H))) =
      ‖P.starProjection (b i : H)‖ ^ 2 := by
  calc
    inner ℝ (b i : H) (Q.starProjection (P.starProjection (b i : H))) =
        inner ℝ (Q.starProjection (b i : H)) (P.starProjection (b i : H)) := by
      rw [Submodule.inner_starProjection_left_eq_right]
    _ = inner ℝ (b i : H) (P.starProjection (b i : H)) := by
      rw [Submodule.starProjection_eq_self_iff.mpr (b i).property]
    _ = ‖P.starProjection (b i : H)‖ ^ 2 := by
      simpa [real_inner_comm] using Submodule.re_inner_starProjection_eq_normSq P (b i : H)

/-- Equation (28): overlap is the sum of squared projection lengths over any
orthonormal basis of the second subspace. -/
theorem subspaceOverlap_eq_sum_norm_projection
    (P Q : Submodule ℝ H) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ Q) :
    subspaceOverlap P Q = ∑ i, ‖P.starProjection (b i : H)‖ ^ 2 := by
  let p : H →ₗ[ℝ] H := P.starProjection.toLinearMap
  let q : H →ₗ[ℝ] H := Q.starProjection.toLinearMap
  let f : H →ₗ[ℝ] H := q * p
  have hf : ∀ x, f x ∈ Q := fun x => Q.starProjection_apply_mem (p x)
  have hf' : ∀ x ∈ Q, f x ∈ Q := fun x _ => hf x
  calc
    subspaceOverlap P Q = LinearMap.trace ℝ H f := by
      exact LinearMap.trace_mul_comm ℝ p q
    _ = LinearMap.trace ℝ Q (f.restrict hf') := by
      exact (LinearMap.trace_restrict_eq_of_forall_mem Q f hf hf').symm
    _ = ∑ i, inner ℝ (b i) ((f.restrict hf') (b i)) :=
      LinearMap.trace_eq_sum_inner (f.restrict hf') b
    _ = ∑ i, ‖P.starProjection (b i : H)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      change inner ℝ (b i : H)
          (Q.starProjection (P.starProjection (b i : H))) = _
      exact restrictedOverlap_inner_eq_norm_sq P Q b i

/-- The canonical finite-basis form of equation (28). -/
theorem subspaceOverlap_eq_sum_stdOrthonormalBasis (P Q : Submodule ℝ H) :
    subspaceOverlap P Q =
      ∑ i : Fin (Module.finrank ℝ Q),
        ‖P.starProjection ((stdOrthonormalBasis ℝ Q) i : H)‖ ^ 2 :=
  subspaceOverlap_eq_sum_norm_projection P Q (stdOrthonormalBasis ℝ Q)

theorem subspaceOverlap_nonneg (P Q : Submodule ℝ H) :
    0 ≤ subspaceOverlap P Q := by
  rw [subspaceOverlap_eq_sum_stdOrthonormalBasis]
  positivity

/-- The overlap cannot exceed the dimension of its second argument. -/
theorem subspaceOverlap_le_finrank_right (P Q : Submodule ℝ H) :
    subspaceOverlap P Q ≤ Module.finrank ℝ Q := by
  rw [subspaceOverlap_eq_sum_stdOrthonormalBasis]
  calc
    (∑ i : Fin (Module.finrank ℝ Q),
        ‖P.starProjection ((stdOrthonormalBasis ℝ Q) i : H)‖ ^ 2) ≤
        ∑ _i : Fin (Module.finrank ℝ Q), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hnorm := P.norm_starProjection_apply_le
        ((stdOrthonormalBasis ℝ Q) i : H)
      have hb : ‖((stdOrthonormalBasis ℝ Q) i : Q)‖ = 1 :=
        (stdOrthonormalBasis ℝ Q).norm_eq_one i
      change ‖((stdOrthonormalBasis ℝ Q) i : H)‖ = 1 at hb
      rw [hb] at hnorm
      nlinarith [norm_nonneg (P.starProjection ((stdOrthonormalBasis ℝ Q) i : H))]
    _ = Module.finrank ℝ Q := by simp

theorem subspaceOverlap_le_finrank_left (P Q : Submodule ℝ H) :
    subspaceOverlap P Q ≤ Module.finrank ℝ P := by
  rw [subspaceOverlap_comm]
  exact subspaceOverlap_le_finrank_right Q P

/-- If `Q ≤ P`, every direction of `Q` projects with full length. -/
theorem subspaceOverlap_eq_finrank_of_le {P Q : Submodule ℝ H} (hQP : Q ≤ P) :
    subspaceOverlap P Q = Module.finrank ℝ Q := by
  rw [subspaceOverlap_eq_sum_stdOrthonormalBasis]
  calc
    (∑ i : Fin (Module.finrank ℝ Q),
        ‖P.starProjection ((stdOrthonormalBasis ℝ Q) i : H)‖ ^ 2) =
        ∑ _i : Fin (Module.finrank ℝ Q), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      have hproj := Submodule.norm_starProjection_apply P
        (hQP (stdOrthonormalBasis ℝ Q i).property)
      have hb := (stdOrthonormalBasis ℝ Q).norm_eq_one i
      change ‖((stdOrthonormalBasis ℝ Q) i : H)‖ = 1 at hb
      rw [hproj, hb, one_pow]
    _ = Module.finrank ℝ Q := by simp

/-- If `P` and `Q` are orthogonal, their overlap vanishes. -/
theorem subspaceOverlap_eq_zero_of_le_orthogonal {P Q : Submodule ℝ H}
    (hPQ : Q ≤ Pᗮ) : subspaceOverlap P Q = 0 := by
  rw [subspaceOverlap_eq_sum_stdOrthonormalBasis]
  apply Finset.sum_eq_zero
  intro i _
  have hz : P.starProjection ((stdOrthonormalBasis ℝ Q) i : H) = 0 := by
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact hPQ (stdOrthonormalBasis ℝ Q _).property
  simp [hz]

/-- Equation (27): overlap normalized by the dimension of the reference subspace. -/
def directionalSubspaceMeasure (P Q : Submodule ℝ H) : ℝ :=
  subspaceOverlap P Q / Module.finrank ℝ Q

theorem directionalSubspaceMeasure_eq_average (P Q : Submodule ℝ H) :
    directionalSubspaceMeasure P Q =
      (∑ i : Fin (Module.finrank ℝ Q),
        ‖P.starProjection ((stdOrthonormalBasis ℝ Q) i : H)‖ ^ 2) /
        Module.finrank ℝ Q := by
  rw [directionalSubspaceMeasure, subspaceOverlap_eq_sum_stdOrthonormalBasis]

theorem directionalSubspaceMeasure_eq_one_of_le {P Q : Submodule ℝ H}
    (hQ : Q ≠ ⊥) (hQP : Q ≤ P) : directionalSubspaceMeasure P Q = 1 := by
  rw [directionalSubspaceMeasure, subspaceOverlap_eq_finrank_of_le hQP]
  have hfinNat : 0 < Module.finrank ℝ Q := Submodule.one_le_finrank_iff.mpr hQ
  have hfinReal : (Module.finrank ℝ Q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hfinNat)
  exact div_self hfinReal

theorem directionalSubspaceMeasure_eq_zero_of_le_orthogonal {P Q : Submodule ℝ H}
    (hPQ : Q ≤ Pᗮ) : directionalSubspaceMeasure P Q = 0 := by
  rw [directionalSubspaceMeasure, subspaceOverlap_eq_zero_of_le_orthogonal hPQ,
    zero_div]

theorem directionalSubspaceMeasure_mem_unitInterval (P Q : Submodule ℝ H)
    (hQ : Q ≠ ⊥) : directionalSubspaceMeasure P Q ∈ Set.Icc 0 1 := by
  have hfinNat : 0 < Module.finrank ℝ Q := Submodule.one_le_finrank_iff.mpr hQ
  have hfinReal : 0 < (Module.finrank ℝ Q : ℝ) := by exact_mod_cast hfinNat
  constructor
  · exact div_nonneg (subspaceOverlap_nonneg P Q) hfinReal.le
  · exact (div_le_one hfinReal).mpr (subspaceOverlap_le_finrank_right P Q)

/-- The Frobenius magnitude associated with equation (29). -/
def frobeniusMagnitude {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ℝ :=
  Real.sqrt (frobeniusInner A A)

/-- Equation (29), intrinsically normalized using projector ranks. -/
def symmetricSubspaceCosine (P Q : Submodule ℝ H) : ℝ :=
  subspaceOverlap P Q /
    Real.sqrt ((Module.finrank ℝ P : ℝ) * Module.finrank ℝ Q)

theorem symmetricSubspaceCosine_comm (P Q : Submodule ℝ H) :
    symmetricSubspaceCosine P Q = symmetricSubspaceCosine Q P := by
  rw [symmetricSubspaceCosine, symmetricSubspaceCosine, subspaceOverlap_comm]
  congr 2
  ring

theorem frobeniusInner_projector_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ H) (P : Submodule ℝ H) :
    frobeniusInner (subspaceProjectorMatrix b P) (subspaceProjectorMatrix b P) =
      Module.finrank ℝ P := by
  rw [← subspaceOverlap_eq_frobeniusInner, subspaceOverlap_eq_finrank_of_le le_rfl]

/-- Equation (29) in projector-matrix notation. -/
theorem symmetricSubspaceCosine_eq_frobenius {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ H) (P Q : Submodule ℝ H) :
    symmetricSubspaceCosine P Q =
      frobeniusInner (subspaceProjectorMatrix b P) (subspaceProjectorMatrix b Q) /
        (frobeniusMagnitude (subspaceProjectorMatrix b P) *
          frobeniusMagnitude (subspaceProjectorMatrix b Q)) := by
  rw [symmetricSubspaceCosine,
    subspaceOverlap_eq_frobeniusInner (b := b) (P := P) (Q := Q),
    frobeniusMagnitude, frobeniusMagnitude,
    frobeniusInner_projector_self (b := b) (P := P),
    frobeniusInner_projector_self (b := b) (P := Q)]
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Module.finrank ℝ P)]

end

end IPNPCNS
