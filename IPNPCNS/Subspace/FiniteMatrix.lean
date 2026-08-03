import IPNPCNS.Subspace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Finite matrix representations of subspaces

The paper identifies matrices when they have the same column space.  This module
states that equivalence as equality of ranges of the associated Euclidean linear
maps and proves the transpose-product identity without choosing an SVD or a
Moore--Penrose inverse.
-/

namespace IPNPCNS

noncomputable section

open scoped Matrix

variable {m n p : Type*}
  [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n]
  [Fintype p] [DecidableEq p]

/-- Equation (6): the column space of a finite real matrix. -/
def matrixColumnSpace (A : Matrix m n ℝ) : Submodule ℝ (EuclideanSpace ℝ m) :=
  A.toEuclideanLin.range

/-- The paper's matrix equivalence relation: equality of column spaces. -/
def ColumnEquivalent (A : Matrix m n ℝ) (B : Matrix m p ℝ) : Prop :=
  matrixColumnSpace A = matrixColumnSpace B

omit [Fintype m] [DecidableEq m] in
@[refl]
theorem ColumnEquivalent.refl (A : Matrix m n ℝ) : ColumnEquivalent A A := rfl

omit [Fintype m] [DecidableEq m] in
@[symm]
theorem ColumnEquivalent.symm {A : Matrix m n ℝ} {B : Matrix m p ℝ}
    (h : ColumnEquivalent A B) : ColumnEquivalent B A :=
  Eq.symm h

omit [Fintype m] [DecidableEq m] in
@[trans]
theorem ColumnEquivalent.trans {A : Matrix m n ℝ} {B : Matrix m p ℝ}
    {q : Type*} [Fintype q] [DecidableEq q] {C : Matrix m q ℝ}
    (hAB : ColumnEquivalent A B) (hBC : ColumnEquivalent B C) :
    ColumnEquivalent A C :=
  Eq.trans hAB hBC

/-- Equations (6)--(11): `A` and `A Aᵀ` have exactly the same column space. -/
theorem matrixColumnSpace_mul_transpose (A : Matrix m n ℝ) :
    matrixColumnSpace (A * A.transpose) = matrixColumnSpace A := by
  unfold matrixColumnSpace
  rw [Matrix.toLpLin_mul (q := 2)]
  have hadjoint : A.transpose.toEuclideanLin = A.toEuclideanLin.adjoint := by
    simpa using Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rw [hadjoint]
  exact LinearMap.range_self_comp_adjoint A.toEuclideanLin

/-- The column-space form of `A ∼ A Aᵀ`. -/
theorem columnEquivalent_mul_transpose (A : Matrix m n ℝ) :
    ColumnEquivalent A (A * A.transpose) :=
  (matrixColumnSpace_mul_transpose A).symm

/-- A coordinate-free horizontal concatenation of two finite linear maps. -/
def linearMapSum {E F G : Type*} [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F] [AddCommMonoid G] [Module ℝ G]
    (A : E →ₗ[ℝ] G) (B : F →ₗ[ℝ] G) : E × F →ₗ[ℝ] G where
  toFun x := A x.1 + B x.2
  map_add' x y := by simp [add_assoc, add_left_comm, add_comm]
  map_smul' c x := by simp [smul_add]

/-- Equation (13), intrinsically: concatenating generators realizes the sum of ranges. -/
theorem range_linearMapSum {E F G : Type*} [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F] [AddCommMonoid G] [Module ℝ G]
    (A : E →ₗ[ℝ] G) (B : F →ₗ[ℝ] G) :
    (linearMapSum A B).range = A.range ⊔ B.range := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    exact Submodule.add_mem_sup ⟨x.1, rfl⟩ ⟨x.2, rfl⟩
  · rw [sup_le_iff]
    constructor
    · rintro z ⟨x, rfl⟩
      exact ⟨(x, 0), by simp [linearMapSum]⟩
    · rintro z ⟨y, rfl⟩
      exact ⟨(0, y), by simp [linearMapSum]⟩

/-- The same concatenation equipped with the Hilbert `L²` product on its domain. -/
def linearMapSumL2 {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (A : E →ₗ[ℝ] G) (B : F →ₗ[ℝ] G) : WithLp 2 (E × F) →ₗ[ℝ] G :=
  (linearMapSum A B).comp (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap

theorem range_linearMapSumL2 {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (A : E →ₗ[ℝ] G) (B : F →ₗ[ℝ] G) :
    (linearMapSumL2 A B).range = A.range ⊔ B.range := by
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    exact Submodule.add_mem_sup ⟨(WithLp.ofLp x).1, rfl⟩ ⟨(WithLp.ofLp x).2, rfl⟩
  · rw [sup_le_iff]
    constructor
    · rintro z ⟨x, rfl⟩
      exact ⟨WithLp.toLp 2 (x, 0), by simp [linearMapSumL2, linearMapSum]⟩
    · rintro z ⟨y, rfl⟩
      exact ⟨WithLp.toLp 2 (0, y), by simp [linearMapSumL2, linearMapSum]⟩

/-- The positive operator of a concatenated map has the same range, the
coordinate-free content of `P Pᵀ + Q Qᵀ` in equation (13). -/
theorem range_linearMapSum_self_comp_adjoint
    {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (A : E →ₗ[ℝ] G) (B : F →ₗ[ℝ] G) :
    let C : WithLp 2 (E × F) →ₗ[ℝ] G := linearMapSumL2 A B
    (C ∘ₗ C.adjoint).range =
      A.range ⊔ B.range := by
  dsimp only
  rw [LinearMap.range_self_comp_adjoint, range_linearMapSumL2]

end

end IPNPCNS
