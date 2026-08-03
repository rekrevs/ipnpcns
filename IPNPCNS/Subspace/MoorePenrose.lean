import IPNPCNS.Subspace.FiniteMatrix
import IPNPCNS.Subspace.Comparison
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Moore--Penrose inverses in finite real Hilbert spaces

This file constructs the Moore--Penrose inverse without a full-rank assumption. The
construction restricts a map to the orthogonal complement of its kernel, where it is
an isomorphism onto its range, and extends the inverse by zero on the orthogonal
complement of the range.
-/

namespace IPNPCNS

noncomputable section

open scoped Matrix

section LinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The injective part of `A`, from the orthogonal complement of its kernel to its
range. -/
def effectiveMap (A : E →ₗ[ℝ] F) : A.kerᗮ →ₗ[ℝ] A.range :=
  A.rangeRestrict.domRestrict A.kerᗮ

omit [FiniteDimensional ℝ F] in
/-- Projecting onto the effective domain does not change the value of `A`. -/
theorem apply_starProjection_orthogonal_ker (A : E →ₗ[ℝ] F) (x : E) :
    A (A.kerᗮ.starProjection x) = A x := by
  have hres : x - A.kerᗮ.starProjection x ∈ A.ker := by
    have horth : x - A.kerᗮ.starProjection x ∈ A.kerᗮᗮ :=
      Submodule.sub_starProjection_mem_orthogonal x
    rw [Submodule.orthogonal_orthogonal] at horth
    exact horth
  have hzero : A (x - A.kerᗮ.starProjection x) = 0 :=
    LinearMap.mem_ker.mp hres
  simpa [map_sub, sub_eq_zero] using hzero

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The effective restriction of `A` is injective. -/
theorem effectiveMap_injective (A : E →ₗ[ℝ] F) :
    Function.Injective (effectiveMap A) := by
  intro x y hxy
  apply Subtype.ext
  have hAxy : A (x - y : E) = 0 := by
    simpa [effectiveMap, map_sub, sub_eq_zero] using congrArg Subtype.val hxy
  have hker : (x - y : E) ∈ A.ker := LinearMap.mem_ker.mpr hAxy
  have horth : (x - y : E) ∈ A.kerᗮ := A.kerᗮ.sub_mem x.property y.property
  have hinner : inner ℝ (x - y : E) (x - y : E) = 0 :=
    (A.ker.mem_orthogonal' (x - y : E)).mp horth _ hker
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hinner)

omit [FiniteDimensional ℝ F] in
/-- The effective restriction of `A` is surjective onto its range. -/
theorem effectiveMap_surjective (A : E →ₗ[ℝ] F) :
    Function.Surjective (effectiveMap A) := by
  intro y
  rcases y.property with ⟨x, hx⟩
  let px : A.kerᗮ :=
    ⟨A.kerᗮ.starProjection x, A.kerᗮ.starProjection_apply_mem x⟩
  refine ⟨px, ?_⟩
  apply Subtype.ext
  change A (A.kerᗮ.starProjection x) = y
  rw [apply_starProjection_orthogonal_ker]
  exact hx

/-- The effective restriction of `A` as a linear equivalence. -/
def effectiveEquiv (A : E →ₗ[ℝ] F) : A.kerᗮ ≃ₗ[ℝ] A.range :=
  LinearEquiv.ofBijective (effectiveMap A)
    ⟨effectiveMap_injective A, effectiveMap_surjective A⟩

omit [FiniteDimensional ℝ F] in
@[simp]
theorem effectiveEquiv_apply (A : E →ₗ[ℝ] F) (x : A.kerᗮ) :
    effectiveEquiv A x = effectiveMap A x :=
  rfl

/-- The Moore--Penrose inverse of a finite-dimensional real linear map. -/
def moorePenroseInverse (A : E →ₗ[ℝ] F) : F →ₗ[ℝ] E :=
  A.kerᗮ.subtype.comp
    ((effectiveEquiv A).symm.toLinearMap.comp A.range.orthogonalProjectionOnto.toLinearMap)

omit [FiniteDimensional ℝ F] in
/-- The Moore--Penrose inverse always lands in the effective domain `ker(A)ᗮ`. -/
theorem moorePenroseInverse_mem_orthogonal_ker (A : E →ₗ[ℝ] F) (y : F) :
    moorePenroseInverse A y ∈ A.kerᗮ :=
  (effectiveEquiv A).symm (A.range.orthogonalProjectionOnto y) |>.property

omit [FiniteDimensional ℝ F] in
/-- Applying `A` after its Moore--Penrose inverse is projection onto `range A`. -/
theorem apply_moorePenroseInverse (A : E →ₗ[ℝ] F) (y : F) :
    A (moorePenroseInverse A y) = A.range.starProjection y := by
  change A ((effectiveEquiv A).symm (A.range.orthogonalProjectionOnto y)) = _
  have h := (effectiveEquiv A).apply_symm_apply (A.range.orthogonalProjectionOnto y)
  exact congrArg Subtype.val h

omit [FiniteDimensional ℝ F] in
/-- Applying the Moore--Penrose inverse after `A` is projection onto `ker(A)ᗮ`. -/
theorem moorePenroseInverse_apply (A : E →ₗ[ℝ] F) (x : E) :
    moorePenroseInverse A (A x) = A.kerᗮ.starProjection x := by
  let px : A.kerᗮ :=
    ⟨A.kerᗮ.starProjection x, A.kerᗮ.starProjection_apply_mem x⟩
  have hrange : A x ∈ A.range := LinearMap.mem_range_self A x
  have hproj : A.range.orthogonalProjectionOnto (A x) =
      (⟨A x, hrange⟩ : A.range) := by
    exact A.range.orthogonalProjectionOnto_mem_subspace_eq_self ⟨A x, hrange⟩
  change ((effectiveEquiv A).symm (A.range.orthogonalProjectionOnto (A x)) : E) = _
  rw [hproj]
  have heffective : effectiveEquiv A px = (⟨A x, hrange⟩ : A.range) := by
    apply Subtype.ext
    exact apply_starProjection_orthogonal_ker A x
  rw [← heffective, (effectiveEquiv A).symm_apply_apply]

omit [FiniteDimensional ℝ F] in
/-- First canonical product identity: `A A⁺` is the range projector. -/
theorem comp_moorePenroseInverse (A : E →ₗ[ℝ] F) :
    A.comp (moorePenroseInverse A) = A.range.starProjection.toLinearMap := by
  ext y
  exact apply_moorePenroseInverse A y

omit [FiniteDimensional ℝ F] in
/-- Second canonical product identity: `A⁺ A` is the projector onto `ker(A)ᗮ`. -/
theorem moorePenroseInverse_comp (A : E →ₗ[ℝ] F) :
    (moorePenroseInverse A).comp A = A.kerᗮ.starProjection.toLinearMap := by
  ext x
  exact moorePenroseInverse_apply A x

omit [FiniteDimensional ℝ F] in
/-- First Penrose equation: `A A⁺ A = A`. -/
theorem moorePenrose_first (A : E →ₗ[ℝ] F) :
    (A.comp (moorePenroseInverse A)).comp A = A := by
  ext x
  change A (moorePenroseInverse A (A x)) = A x
  rw [moorePenroseInverse_apply, apply_starProjection_orthogonal_ker]

omit [FiniteDimensional ℝ F] in
/-- Second Penrose equation: `A⁺ A A⁺ = A⁺`. -/
theorem moorePenrose_second (A : E →ₗ[ℝ] F) :
    ((moorePenroseInverse A).comp A).comp (moorePenroseInverse A) =
      moorePenroseInverse A := by
  ext y
  change moorePenroseInverse A (A (moorePenroseInverse A y)) =
    moorePenroseInverse A y
  rw [moorePenroseInverse_apply]
  exact A.kerᗮ.starProjection_eq_self_iff.mpr
    (moorePenroseInverse_mem_orthogonal_ker A y)

/-- Third Penrose equation: `A A⁺` is self-adjoint. -/
theorem moorePenrose_third (A : E →ₗ[ℝ] F) :
    (A.comp (moorePenroseInverse A)).adjoint =
      A.comp (moorePenroseInverse A) := by
  rw [comp_moorePenroseInverse]
  exact A.range.starProjection_isSymmetric.adjoint_eq

omit [FiniteDimensional ℝ F] in
/-- Fourth Penrose equation: `A⁺ A` is self-adjoint. -/
theorem moorePenrose_fourth (A : E →ₗ[ℝ] F) :
    ((moorePenroseInverse A).comp A).adjoint =
      (moorePenroseInverse A).comp A := by
  rw [moorePenroseInverse_comp]
  exact A.kerᗮ.starProjection_isSymmetric.adjoint_eq

/-- The four equations that characterize a Moore--Penrose inverse. -/
structure IsMoorePenroseInverse (A : E →ₗ[ℝ] F) (B : F →ₗ[ℝ] E) : Prop where
  first : (A.comp B).comp A = A
  second : (B.comp A).comp B = B
  third : (A.comp B).adjoint = A.comp B
  fourth : (B.comp A).adjoint = B.comp A

/-- The constructed inverse satisfies the complete Moore--Penrose specification. -/
theorem moorePenroseInverse_spec (A : E →ₗ[ℝ] F) :
    IsMoorePenroseInverse A (moorePenroseInverse A) where
  first := moorePenrose_first A
  second := moorePenrose_second A
  third := moorePenrose_third A
  fourth := moorePenrose_fourth A

/-- Any map satisfying the Penrose equations has `A B` equal to the orthogonal
projector onto `range A`. -/
theorem IsMoorePenroseInverse.comp_eq_range_projection
    {A : E →ₗ[ℝ] F} {B : F →ₗ[ℝ] E} (h : IsMoorePenroseInverse A B) :
    A.comp B = A.range.starProjection.toLinearMap := by
  let T : F →ₗ[ℝ] F := A.comp B
  have hidem : IsIdempotentElem T := by
    unfold IsIdempotentElem
    ext y
    change A (B (A (B y))) = A (B y)
    exact DFunLike.congr_fun h.first (B y)
  have hsym : T.IsSymmetric :=
    (LinearMap.eq_adjoint_iff T T).mp h.third.symm
  have hproj : T.IsSymmetricProjection := ⟨hidem, hsym⟩
  have hrange : T.range = A.range := by
    apply le_antisymm
    · exact LinearMap.range_comp_le_range B A
    · rintro _ ⟨x, rfl⟩
      refine ⟨A x, ?_⟩
      change A (B (A x)) = A x
      exact DFunLike.congr_fun h.first x
  exact hproj.ext (Submodule.isSymmetricProjection_starProjection A.range) (by
    simpa using hrange)

/-- Any map satisfying the Penrose equations takes values in `ker(A)ᗮ`. -/
theorem IsMoorePenroseInverse.mem_orthogonal_ker
    {A : E →ₗ[ℝ] F} {B : F →ₗ[ℝ] E} (h : IsMoorePenroseInverse A B) (y : F) :
    B y ∈ A.kerᗮ := by
  rw [A.ker.mem_orthogonal']
  intro z hz
  have hsym : (B.comp A).IsSymmetric :=
    (LinearMap.eq_adjoint_iff (B.comp A) (B.comp A)).mp h.fourth.symm
  have hfix : B (A (B y)) = B y := by
    exact DFunLike.congr_fun h.second y
  calc
    inner ℝ (B y) z = inner ℝ (B (A (B y))) z := by rw [hfix]
    _ = inner ℝ (B y) (B (A z)) := hsym (B y) z
    _ = 0 := by simp [LinearMap.mem_ker.mp hz]

/-- The four Penrose equations determine the inverse uniquely. -/
theorem moorePenroseInverse_unique
    {A : E →ₗ[ℝ] F} {B : F →ₗ[ℝ] E} (h : IsMoorePenroseInverse A B) :
    B = moorePenroseInverse A := by
  ext y
  let byEffective : A.kerᗮ := ⟨B y, h.mem_orthogonal_ker y⟩
  let mpEffective : A.kerᗮ :=
    ⟨moorePenroseInverse A y, moorePenroseInverse_mem_orthogonal_ker A y⟩
  have hAeq : A (B y) = A (moorePenroseInverse A y) := by
    rw [apply_moorePenroseInverse]
    exact DFunLike.congr_fun h.comp_eq_range_projection y
  have heffective : effectiveMap A byEffective = effectiveMap A mpEffective := by
    apply Subtype.ext
    exact hAeq
  exact congrArg Subtype.val (effectiveMap_injective A heffective)

/-- The second canonical product is projection onto the row space, represented
coordinate-free as `range A†`. -/
theorem moorePenroseInverse_comp_eq_adjoint_range_projection (A : E →ₗ[ℝ] F) :
    (moorePenroseInverse A).comp A = A.adjoint.range.starProjection.toLinearMap := by
  rw [moorePenroseInverse_comp]
  have hsub : A.kerᗮ = A.adjoint.range := A.orthogonal_ker
  ext x
  apply Eq.symm
  apply A.adjoint.range.eq_starProjection_of_mem_orthogonal
  · rw [← hsub]
    exact A.kerᗮ.starProjection_apply_mem x
  · rw [← hsub]
    exact Submodule.sub_starProjection_mem_orthogonal x

omit [FiniteDimensional ℝ F] in
/-- An injective map has a Moore--Penrose left inverse. -/
theorem moorePenroseInverse_leftInverse (A : E →ₗ[ℝ] F)
    (hA : Function.Injective A) : Function.LeftInverse (moorePenroseInverse A) A := by
  intro x
  rw [moorePenroseInverse_apply]
  have hker : A.ker = ⊥ := LinearMap.ker_eq_bot.mpr hA
  have hmem : x ∈ A.kerᗮ := by simp [hker]
  exact A.kerᗮ.starProjection_eq_self_iff.mpr hmem

omit [FiniteDimensional ℝ F] in
/-- A surjective map has a Moore--Penrose right inverse. -/
theorem moorePenroseInverse_rightInverse (A : E →ₗ[ℝ] F)
    (hA : Function.Surjective A) : Function.RightInverse (moorePenroseInverse A) A := by
  intro y
  rw [apply_moorePenroseInverse]
  have hrange : A.range = ⊤ := LinearMap.range_eq_top.mpr hA
  exact A.range.starProjection_eq_self_iff.mpr (by simp [hrange])

omit [FiniteDimensional ℝ F] in
/-- The Moore--Penrose inverse of the zero map is zero. -/
@[simp]
theorem moorePenroseInverse_zero :
    moorePenroseInverse (0 : E →ₗ[ℝ] F) = 0 := by
  ext y
  have hmem := moorePenroseInverse_mem_orthogonal_ker (0 : E →ₗ[ℝ] F) y
  simpa using hmem

end LinearMap

section ProjectionHelpers

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Equal finite-dimensional subspaces have equal orthogonal projectors. This
extensional lemma avoids dependence on the particular projection-instance proof. -/
theorem starProjection_eq_of_submodule_eq {P Q : Submodule ℝ H} (hPQ : P = Q) :
    P.starProjection.toLinearMap = Q.starProjection.toLinearMap := by
  ext x
  apply Eq.symm
  apply Q.eq_starProjection_of_mem_orthogonal
  · rw [← hPQ]
    exact P.starProjection_apply_mem x
  · rw [← hPQ]
    exact Submodule.sub_starProjection_mem_orthogonal x

/-- On a vector from `P`, projecting onto the rejection space `P ¬ Q` reproduces
the original rejection from `Q`. -/
theorem subspaceRejection_starProjection_apply
    (P Q : Submodule ℝ H) {x : H} (hx : x ∈ P) :
    (subspaceRejection P Q).starProjection x = Qᗮ.starProjection x := by
  apply (subspaceRejection P Q).eq_starProjection_of_mem_orthogonal
  · exact ⟨x, hx, rfl⟩
  · rw [(subspaceRejection P Q).mem_orthogonal']
    intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    have hdecomp : x - Qᗮ.starProjection x = Q.starProjection x := by
      rw [Q.starProjection_orthogonal_val]
      abel
    rw [hdecomp]
    exact Submodule.inner_right_of_mem_orthogonal
      (Q.starProjection_apply_mem x) (Qᗮ.starProjection_apply_mem u)

/-- The sum of two orthogonal projectors has range equal to the sum of their
subspaces. This justifies the positive-semidefinite sum used in equation (22). -/
theorem range_add_starProjection (P Q : Submodule ℝ H) :
    (P.starProjection.toLinearMap + Q.starProjection.toLinearMap).range = P ⊔ Q := by
  let T : H →ₗ[ℝ] H :=
    P.starProjection.toLinearMap + Q.starProjection.toLinearMap
  have hker : T.ker = Pᗮ ⊓ Qᗮ := by
    apply le_antisymm
    · intro x hx
      have hzero : P.starProjection x + Q.starProjection x = 0 := by
        exact LinearMap.mem_ker.mp hx
      have hpInner : inner ℝ x (P.starProjection x) =
          ‖P.starProjection x‖ ^ 2 := by
        simpa [real_inner_comm] using
          Submodule.re_inner_starProjection_eq_normSq P x
      have hqInner : inner ℝ x (Q.starProjection x) =
          ‖Q.starProjection x‖ ^ 2 := by
        simpa [real_inner_comm] using
          Submodule.re_inner_starProjection_eq_normSq Q x
      have hsum : ‖P.starProjection x‖ ^ 2 + ‖Q.starProjection x‖ ^ 2 = 0 := by
        calc
          ‖P.starProjection x‖ ^ 2 + ‖Q.starProjection x‖ ^ 2 =
              inner ℝ x (P.starProjection x) + inner ℝ x (Q.starProjection x) := by
            rw [hpInner, hqInner]
          _ = inner ℝ x (P.starProjection x + Q.starProjection x) := by
            rw [inner_add_right]
          _ = 0 := by rw [hzero, inner_zero_right]
      have hpSq : ‖P.starProjection x‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖P.starProjection x‖,
          sq_nonneg ‖Q.starProjection x‖]
      have hqSq : ‖Q.starProjection x‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖P.starProjection x‖,
          sq_nonneg ‖Q.starProjection x‖]
      have hpZero : P.starProjection x = 0 :=
        norm_eq_zero.mp (sq_eq_zero_iff.mp hpSq)
      have hqZero : Q.starProjection x = 0 :=
        norm_eq_zero.mp (sq_eq_zero_iff.mp hqSq)
      exact ⟨P.starProjection_apply_eq_zero_iff.mp hpZero,
        Q.starProjection_apply_eq_zero_iff.mp hqZero⟩
    · rintro x ⟨hxP, hxQ⟩
      apply LinearMap.mem_ker.mpr
      change P.starProjection x + Q.starProjection x = 0
      rw [P.starProjection_apply_eq_zero_iff.mpr hxP,
        Q.starProjection_apply_eq_zero_iff.mpr hxQ, add_zero]
  have hsym : T.IsSymmetric :=
    P.starProjection_isSymmetric.add Q.starProjection_isSymmetric
  calc
    T.range = T.kerᗮ := by
      rw [← hsym.orthogonal_range, Submodule.orthogonal_orthogonal]
    _ = (Pᗮ ⊓ Qᗮ)ᗮ := by rw [hker]
    _ = (P ⊔ Q)ᗮᗮ := by rw [orthogonal_sup_eq_inf_orthogonal]
    _ = P ⊔ Q := Submodule.orthogonal_orthogonal _

end ProjectionHelpers

section Matrix

variable {m n : Type*}
  [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n]

/-- The Moore--Penrose inverse of an arbitrary finite rectangular real matrix. -/
def matrixMoorePenroseInverse (A : Matrix m n ℝ) : Matrix n m ℝ :=
  (Matrix.toEuclideanLin :
      Matrix n m ℝ ≃ₗ[ℝ]
        EuclideanSpace ℝ m →ₗ[ℝ] EuclideanSpace ℝ n).symm
    (moorePenroseInverse A.toEuclideanLin)

/-- The canonical orthogonal projector generated by a matrix. -/
def matrixProjector (A : Matrix m n ℝ) : Matrix m m ℝ :=
  A * matrixMoorePenroseInverse A

/-- The matrix construction transports exactly to the linear-map construction. -/
@[simp]
theorem toEuclideanLin_matrixMoorePenroseInverse (A : Matrix m n ℝ) :
    (matrixMoorePenroseInverse A).toEuclideanLin =
      moorePenroseInverse A.toEuclideanLin := by
  simp [matrixMoorePenroseInverse]

/-- First matrix Penrose equation. -/
theorem matrixMoorePenrose_first (A : Matrix m n ℝ) :
    (A * matrixMoorePenroseInverse A) * A = A := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul (q := 2), Matrix.toLpLin_mul (q := 2),
    toEuclideanLin_matrixMoorePenroseInverse]
  exact moorePenrose_first A.toEuclideanLin

/-- Second matrix Penrose equation. -/
theorem matrixMoorePenrose_second (A : Matrix m n ℝ) :
    (matrixMoorePenroseInverse A * A) * matrixMoorePenroseInverse A =
      matrixMoorePenroseInverse A := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul (q := 2), Matrix.toLpLin_mul (q := 2),
    toEuclideanLin_matrixMoorePenroseInverse]
  exact moorePenrose_second A.toEuclideanLin

/-- Third matrix Penrose equation. -/
theorem matrixMoorePenrose_third (A : Matrix m n ℝ) :
    (A * matrixMoorePenroseInverse A).transpose =
      A * matrixMoorePenroseInverse A := by
  apply Matrix.toEuclideanLin.injective
  have hadjoint :
      (A * matrixMoorePenroseInverse A).transpose.toEuclideanLin =
        (A * matrixMoorePenroseInverse A).toEuclideanLin.adjoint := by
    simpa using Matrix.toEuclideanLin_conjTranspose_eq_adjoint
      (A * matrixMoorePenroseInverse A)
  rw [hadjoint, Matrix.toLpLin_mul (q := 2),
    toEuclideanLin_matrixMoorePenroseInverse]
  exact moorePenrose_third A.toEuclideanLin

/-- Fourth matrix Penrose equation. -/
theorem matrixMoorePenrose_fourth (A : Matrix m n ℝ) :
    (matrixMoorePenroseInverse A * A).transpose =
      matrixMoorePenroseInverse A * A := by
  apply Matrix.toEuclideanLin.injective
  have hadjoint :
      (matrixMoorePenroseInverse A * A).transpose.toEuclideanLin =
        (matrixMoorePenroseInverse A * A).toEuclideanLin.adjoint := by
    simpa using Matrix.toEuclideanLin_conjTranspose_eq_adjoint
      (matrixMoorePenroseInverse A * A)
  rw [hadjoint, Matrix.toLpLin_mul (q := 2),
    toEuclideanLin_matrixMoorePenroseInverse]
  exact moorePenrose_fourth A.toEuclideanLin

/-- `A A⁺` is exactly the Euclidean orthogonal projector onto `Col(A)`. -/
theorem toEuclideanLin_mul_matrixMoorePenroseInverse (A : Matrix m n ℝ) :
    (A * matrixMoorePenroseInverse A).toEuclideanLin =
      (matrixColumnSpace A).starProjection.toLinearMap := by
  rw [Matrix.toLpLin_mul (q := 2),
    toEuclideanLin_matrixMoorePenroseInverse]
  exact comp_moorePenroseInverse A.toEuclideanLin

@[simp]
theorem toEuclideanLin_matrixProjector (A : Matrix m n ℝ) :
    (matrixProjector A).toEuclideanLin =
      (matrixColumnSpace A).starProjection.toLinearMap :=
  toEuclideanLin_mul_matrixMoorePenroseInverse A

/-- `A⁺ A` is exactly the Euclidean orthogonal projector onto the row space of `A`. -/
theorem toEuclideanLin_matrixMoorePenroseInverse_mul (A : Matrix m n ℝ) :
    (matrixMoorePenroseInverse A * A).toEuclideanLin =
      A.toEuclideanLin.adjoint.range.starProjection.toLinearMap := by
  rw [Matrix.toLpLin_mul (q := 2),
    toEuclideanLin_matrixMoorePenroseInverse]
  exact moorePenroseInverse_comp_eq_adjoint_range_projection A.toEuclideanLin

/-- The canonical projector `A A⁺` has exactly the column space of `A`, including
for zero and rank-deficient matrices. -/
theorem matrixColumnSpace_mul_matrixMoorePenroseInverse (A : Matrix m n ℝ) :
    matrixColumnSpace (A * matrixMoorePenroseInverse A) = matrixColumnSpace A := by
  unfold matrixColumnSpace
  rw [toEuclideanLin_mul_matrixMoorePenroseInverse]
  exact Submodule.range_starProjection _

@[simp]
theorem matrixColumnSpace_matrixProjector (A : Matrix m n ℝ) :
    matrixColumnSpace (matrixProjector A) = matrixColumnSpace A :=
  matrixColumnSpace_mul_matrixMoorePenroseInverse A

/-- In standard Euclidean coordinates, the existing intrinsic projector matrix is
the matrix of `starProjection`. -/
theorem toEuclideanLin_subspaceProjectorMatrix
    (P : Submodule ℝ (EuclideanSpace ℝ m)) :
    (subspaceProjectorMatrix (EuclideanSpace.basisFun m ℝ) P).toEuclideanLin =
      P.starProjection.toLinearMap := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  simp [subspaceProjectorMatrix]

/-- The paper's canonical projector identity `A A⁺ = P_Col(A)`. -/
theorem mul_matrixMoorePenroseInverse_eq_projectorMatrix (A : Matrix m n ℝ) :
    A * matrixMoorePenroseInverse A =
      subspaceProjectorMatrix (EuclideanSpace.basisFun m ℝ) (matrixColumnSpace A) := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_mul_matrixMoorePenroseInverse,
    toEuclideanLin_subspaceProjectorMatrix]

/-- The canonical matrix projector agrees with the intrinsic projector matrix. -/
theorem matrixProjector_eq_projectorMatrix (A : Matrix m n ℝ) :
    matrixProjector A =
      subspaceProjectorMatrix (EuclideanSpace.basisFun m ℝ) (matrixColumnSpace A) :=
  mul_matrixMoorePenroseInverse_eq_projectorMatrix A

/-- The transpose represents the row space as the range of the adjoint. -/
theorem matrixColumnSpace_transpose (A : Matrix m n ℝ) :
    matrixColumnSpace A.transpose = A.toEuclideanLin.adjoint.range := by
  unfold matrixColumnSpace
  have hadjoint : A.transpose.toEuclideanLin = A.toEuclideanLin.adjoint := by
    simpa using Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rw [hadjoint]

/-- The second canonical projector identity `A⁺ A = P_Row(A)`. -/
theorem matrixMoorePenroseInverse_mul_eq_rowProjectorMatrix (A : Matrix m n ℝ) :
    matrixMoorePenroseInverse A * A =
      subspaceProjectorMatrix (EuclideanSpace.basisFun n ℝ)
        (matrixColumnSpace A.transpose) := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_matrixMoorePenroseInverse_mul,
    toEuclideanLin_subspaceProjectorMatrix, matrixColumnSpace_transpose]

/-- Equation (12): subtracting the canonical projector from the identity gives the
projector onto the orthogonal complement. -/
theorem one_sub_matrixProjector_eq_orthogonalProjectorMatrix (A : Matrix m n ℝ) :
    1 - matrixProjector A =
      subspaceProjectorMatrix (EuclideanSpace.basisFun m ℝ)
        (matrixColumnSpace A)ᗮ := by
  rw [matrixProjector_eq_projectorMatrix]
  exact (subspaceProjectorMatrix_orthogonal
    (EuclideanSpace.basisFun m ℝ) (matrixColumnSpace A)).symm

/-- The column-space form of equation (12). -/
theorem matrixColumnSpace_one_sub_matrixProjector (A : Matrix m n ℝ) :
    matrixColumnSpace (1 - matrixProjector A) = (matrixColumnSpace A)ᗮ := by
  rw [one_sub_matrixProjector_eq_orthogonalProjectorMatrix]
  unfold matrixColumnSpace
  rw [toEuclideanLin_subspaceProjectorMatrix]
  exact Submodule.range_starProjection _

/-- The Moore--Penrose inverse of the zero matrix is the zero matrix. -/
@[simp]
theorem matrixMoorePenroseInverse_zero :
    matrixMoorePenroseInverse (0 : Matrix m n ℝ) = 0 := by
  apply Matrix.toEuclideanLin.injective
  simp

/-- A nonzero vector in the prediction kernel witnesses that the row projector
`A⁺ A` is not the identity. -/
theorem matrixMoorePenroseInverse_mul_ne_one_of_mem_ker
    (A : Matrix m n ℝ) {x : EuclideanSpace ℝ n}
    (hx : A.toEuclideanLin x = 0) (hx0 : x ≠ 0) :
    matrixMoorePenroseInverse A * A ≠ 1 := by
  intro hOne
  have hMap := congrArg Matrix.toEuclideanLin hOne
  have hxMap := DFunLike.congr_fun hMap x
  rw [Matrix.toLpLin_mul (q := 2),
    toEuclideanLin_matrixMoorePenroseInverse] at hxMap
  have hxMap' :
      moorePenroseInverse A.toEuclideanLin (A.toEuclideanLin x) = x := by
    simpa only [LinearMap.comp_apply, Matrix.toLpLin_one, LinearMap.id_apply] using hxMap
  rw [hx, map_zero] at hxMap'
  exact hx0 hxMap'.symm

end Matrix

section PaperRepresentations

variable {m n p : Type*}
  [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n]
  [Fintype p] [DecidableEq p]

/-- Equation (15): multiplying the two canonical projector matrices represents the
intrinsic projection of one column space onto the other. -/
theorem matrixColumnSpace_projector_mul_projector
    (P : Matrix m n ℝ) (Q : Matrix m p ℝ) :
    matrixColumnSpace (matrixProjector Q * matrixProjector P) =
      subspaceProjection (matrixColumnSpace P) (matrixColumnSpace Q) := by
  unfold matrixColumnSpace
  rw [Matrix.toLpLin_mul (q := 2), toEuclideanLin_matrixProjector,
    toEuclideanLin_matrixProjector]
  exact (subspaceProjection_eq_range_comp
    (matrixColumnSpace P) (matrixColumnSpace Q)).symm

/-- The shortened form of equation (15): the rightmost canonical projector can be
replaced by the original generator matrix. -/
theorem matrixColumnSpace_projector_mul
    (P : Matrix m n ℝ) (Q : Matrix m p ℝ) :
    matrixColumnSpace (matrixProjector Q * P) =
      subspaceProjection (matrixColumnSpace P) (matrixColumnSpace Q) := by
  change (matrixProjector Q * P).toEuclideanLin.range =
    subspaceProjection (matrixColumnSpace P) (matrixColumnSpace Q)
  rw [Matrix.toLpLin_mul (q := 2)]
  unfold subspaceProjection
  rw [toEuclideanLin_matrixProjector, LinearMap.range_comp]
  rfl

/-- The two matrix renderings in equation (15) are column-equivalent. -/
theorem columnEquivalent_projection_renderings
    (P : Matrix m n ℝ) (Q : Matrix m p ℝ) :
    ColumnEquivalent (matrixProjector Q * matrixProjector P)
      (matrixProjector Q * P) := by
  unfold ColumnEquivalent
  rw [matrixColumnSpace_projector_mul_projector,
    matrixColumnSpace_projector_mul]

/-- Equation (16): multiplying by the complementary canonical projector represents
orthogonal rejection. -/
theorem matrixColumnSpace_rejection
    (P : Matrix m n ℝ) (Q : Matrix m p ℝ) :
    matrixColumnSpace ((1 - matrixProjector Q) * P) =
      subspaceRejection (matrixColumnSpace P) (matrixColumnSpace Q) := by
  rw [one_sub_matrixProjector_eq_orthogonalProjectorMatrix]
  unfold matrixColumnSpace subspaceRejection subspaceProjection
  rw [Matrix.toLpLin_mul (q := 2),
    toEuclideanLin_subspaceProjectorMatrix, LinearMap.range_comp]

/-- The operator identity underlying equation (16). -/
theorem toEuclideanLin_rejection
    (P : Matrix m n ℝ) (Q : Matrix m p ℝ) :
    ((1 - matrixProjector Q) * P).toEuclideanLin =
      (matrixColumnSpace Q)ᗮ.starProjection.toLinearMap.comp P.toEuclideanLin := by
  rw [one_sub_matrixProjector_eq_orthogonalProjectorMatrix,
    Matrix.toLpLin_mul (q := 2), toEuclideanLin_subspaceProjectorMatrix]

/-- Equation (19): if `R = (I - Q Q⁺) P`, then projection of `P` onto `Col(R)`
is exactly `R`. -/
theorem rejection_projector_mul_source
    (P : Matrix m n ℝ) (Q : Matrix m p ℝ) :
    let R := (1 - matrixProjector Q) * P
    matrixProjector R * P = R := by
  dsimp only
  let R := (1 - matrixProjector Q) * P
  have hRspace : matrixColumnSpace R =
      subspaceRejection (matrixColumnSpace P) (matrixColumnSpace Q) := by
    exact matrixColumnSpace_rejection P Q
  have hRproj := starProjection_eq_of_submodule_eq hRspace
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul (q := 2), toEuclideanLin_matrixProjector,
    hRproj]
  rw [show R.toEuclideanLin =
      (matrixColumnSpace Q)ᗮ.starProjection.toLinearMap.comp P.toEuclideanLin by
    exact toEuclideanLin_rejection P Q]
  apply LinearMap.ext
  intro x
  exact subspaceRejection_starProjection_apply
    (matrixColumnSpace P) (matrixColumnSpace Q)
      (LinearMap.mem_range_self P.toEuclideanLin x)

/-- Equations (17)--(20), as an exact matrix identity. Double rejection of `P`
through `R = (I - Q Q⁺)P` reduces to the projected generator `Q Q⁺ P`. -/
theorem doubleRejection_matrix_identity
    (P : Matrix m n ℝ) (Q : Matrix m p ℝ) :
    let R := (1 - matrixProjector Q) * P
    (1 - matrixProjector R) * P = matrixProjector Q * P := by
  dsimp only
  let R := (1 - matrixProjector Q) * P
  calc
    (1 - matrixProjector R) * P = P - matrixProjector R * P := by
      rw [Matrix.sub_mul, Matrix.one_mul]
    _ = P - R := by rw [rejection_projector_mul_source P Q]
    _ = matrixProjector Q * P := by
      dsimp [R]
      rw [Matrix.sub_mul, Matrix.one_mul]
      abel

/-- The column-space rendering of equations (17)--(20), connected to T-0009's
intrinsic double-rejection theorem. -/
theorem matrixColumnSpace_doubleRejection
    (P : Matrix m n ℝ) (Q : Matrix m p ℝ) :
    let R := (1 - matrixProjector Q) * P
    matrixColumnSpace ((1 - matrixProjector R) * P) =
      subspaceProjection (matrixColumnSpace P) (matrixColumnSpace Q) := by
  dsimp only
  rw [doubleRejection_matrix_identity, matrixColumnSpace_projector_mul]

/-- The generator `2I - P P⁺ - Q Q⁺` for the sum of the two orthogonal
complements in equation (22). -/
def complementSumGenerator
    (P : Matrix m n ℝ) (Q : Matrix m p ℝ) : Matrix m m ℝ :=
  (1 - matrixProjector P) + (1 - matrixProjector Q)

/-- The complement-sum generator has exactly the expected sum of column spaces. -/
theorem matrixColumnSpace_complementSumGenerator
    (P : Matrix m n ℝ) (Q : Matrix m p ℝ) :
    matrixColumnSpace (complementSumGenerator P Q) =
      (matrixColumnSpace P)ᗮ ⊔ (matrixColumnSpace Q)ᗮ := by
  rw [complementSumGenerator,
    one_sub_matrixProjector_eq_orthogonalProjectorMatrix,
    one_sub_matrixProjector_eq_orthogonalProjectorMatrix]
  change
    ((subspaceProjectorMatrix (EuclideanSpace.basisFun m ℝ) (matrixColumnSpace P)ᗮ +
      subspaceProjectorMatrix (EuclideanSpace.basisFun m ℝ) (matrixColumnSpace Q)ᗮ).toEuclideanLin).range = _
  rw [map_add, toEuclideanLin_subspaceProjectorMatrix,
    toEuclideanLin_subspaceProjectorMatrix]
  exact range_add_starProjection _ _

/-- The complement-sum generator written exactly as the paper's `2I - PP⁺ - QQ⁺`. -/
theorem complementSumGenerator_eq_two_identity_sub
    (P : Matrix m n ℝ) (Q : Matrix m p ℝ) :
    complementSumGenerator P Q =
      (2 : ℝ) • (1 : Matrix m m ℝ) - matrixProjector P - matrixProjector Q := by
  ext i j
  simp [complementSumGenerator]
  ring

/-- Equation (22): the Moore--Penrose matrix rendering of intersection has column
space `Col(P) ∩ Col(Q)`. -/
theorem matrixColumnSpace_intersection_formula
    (P : Matrix m n ℝ) (Q : Matrix m p ℝ) :
    matrixColumnSpace
        (1 - matrixProjector
          ((2 : ℝ) • (1 : Matrix m m ℝ) - matrixProjector P - matrixProjector Q)) =
      matrixColumnSpace P ⊓ matrixColumnSpace Q := by
  rw [← complementSumGenerator_eq_two_identity_sub,
    matrixColumnSpace_one_sub_matrixProjector,
    matrixColumnSpace_complementSumGenerator]
  exact (inf_eq_orthogonal_sup_orthogonal
    (matrixColumnSpace P) (matrixColumnSpace Q)).symm

end PaperRepresentations

end

end IPNPCNS
