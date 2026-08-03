import IPNPCNS.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Deterministic signal and filter model

This file gives Sections 3.1--3.3 a precise deterministic interface. Signals are
Bochner `L²` equivalence classes on a finite recording window. Spatial matrices act
pointwise, temporal filters are bounded linear operators, and population outputs are
finite nonnegative weighted sums.

The paper does not specify a convolution boundary convention or enough regularity to
derive compactness, a Laplace transfer law, or the `O(Δt²)` term in equation (33).
Those claims therefore appear below only through named, inspectable hypotheses.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal MeasureTheory

namespace IPNPCNS
namespace Signal

noncomputable section

/-- Lebesgue measure restricted to the closed recording window `[0, T]`. When
`T < 0` the interval, and hence the measure, is empty. -/
def recordingMeasure (T : ℝ) : Measure ℝ :=
  volume.restrict (Icc 0 T)

/-- The recording window has the expected finite measure. -/
@[simp]
theorem recordingMeasure_univ (T : ℝ) :
    recordingMeasure T univ = ENNReal.ofReal T := by
  simp [recordingMeasure, Real.volume_Icc]

/-- A Bochner `L²` signal over an arbitrary measured time domain. -/
abbrev L2Signal {Time : Type*} [MeasurableSpace Time]
    (μ : Measure Time) (E : Type*) [NormedAddCommGroup E] :=
  MeasureTheory.Lp E 2 μ

/-- Scalar signals on the paper's finite recording window. -/
abbrev ScalarSignal (T : ℝ) :=
  L2Signal (recordingMeasure T) ℝ

/-- Finite-vector signals on the paper's finite recording window. -/
abbrev VectorSignal (T : ℝ) (n : Type*) [Fintype n] :=
  L2Signal (recordingMeasure T) (EuclideanSpace ℝ n)

section Spatial

variable {Time : Type*} [MeasurableSpace Time] {μ : Measure Time}
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Lift a bounded spatial map pointwise to Bochner `L²`. -/
def liftSpatial (L : E →L[ℝ] F) : L2Signal μ E →L[ℝ] L2Signal μ F :=
  L.compLpL 2 μ

/-- The lifted map agrees almost everywhere with pointwise application. -/
theorem liftSpatial_apply_ae (L : E →L[ℝ] F) (x : L2Signal μ E) :
    liftSpatial (μ := μ) L x =ᵐ[μ] fun t => L (x t) := by
  simpa [liftSpatial] using L.coeFn_compLpL x

/-- Pointwise lifting does not increase the operator norm. -/
theorem norm_liftSpatial_le (L : E →L[ℝ] F) :
    ‖liftSpatial (μ := μ) L‖ ≤ ‖L‖ := by
  simpa [liftSpatial] using L.norm_compLpL_le (p := (2 : ℝ≥0∞)) (μ := μ)

/-- The resulting signal obeys the spatial operator bound. -/
theorem norm_liftSpatial_apply_le (L : E →L[ℝ] F) (x : L2Signal μ E) :
    ‖liftSpatial (μ := μ) L x‖ ≤ ‖L‖ * ‖x‖ := by
  calc
    ‖liftSpatial (μ := μ) L x‖ ≤ ‖liftSpatial (μ := μ) L‖ * ‖x‖ :=
      (liftSpatial (μ := μ) L).le_opNorm x
    _ ≤ ‖L‖ * ‖x‖ := mul_le_mul_of_nonneg_right (norm_liftSpatial_le L) (norm_nonneg x)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- A finite real matrix as a bounded map between Euclidean coordinate spaces. -/
def matrixSpatialMap (A : Matrix m n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

/-- Lift a finite spatial matrix pointwise to vector-valued `L²` signals. -/
def liftMatrix (A : Matrix m n ℝ) :
    L2Signal μ (EuclideanSpace ℝ n) →L[ℝ]
      L2Signal μ (EuclideanSpace ℝ m) :=
  liftSpatial (μ := μ) (matrixSpatialMap A)

/-- The matrix lift has the literal pointwise matrix action almost everywhere. -/
theorem liftMatrix_apply_ae (A : Matrix m n ℝ)
    (x : L2Signal μ (EuclideanSpace ℝ n)) :
    liftMatrix (μ := μ) A x =ᵐ[μ]
      fun t => Matrix.toEuclideanLin A (x t) := by
  simpa [liftMatrix, matrixSpatialMap] using
    liftSpatial_apply_ae (μ := μ) (matrixSpatialMap A) x

end Spatial

section Aggregation

variable {ι S : Type*} [Fintype ι]
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S]

/-- Equation (31): the population signal is a finite weighted sum of individual
outputs. -/
def aggregateSignal (weights : ι → ℝ) (outputs : ι → S) : S :=
  ∑ i, weights i • outputs i

/-- The weighted aggregation map is linear in the output family. -/
theorem aggregateSignal_add (weights : ι → ℝ) (x y : ι → S) :
    aggregateSignal weights (x + y) =
      aggregateSignal weights x + aggregateSignal weights y := by
  simp [aggregateSignal, smul_add, Finset.sum_add_distrib]

/-- Adding two weight maps adds their aggregate outputs. -/
theorem aggregateSignal_add_weights (a b : ι → ℝ) (x : ι → S) :
    aggregateSignal (a + b) x = aggregateSignal a x + aggregateSignal b x := by
  simp [aggregateSignal, add_smul, Finset.sum_add_distrib]

/-- A bounded linear filter commutes exactly with finite population aggregation. -/
theorem map_aggregateSignal (F : S →L[ℝ] S) (weights : ι → ℝ) (outputs : ι → S) :
    F (aggregateSignal weights outputs) =
      aggregateSignal weights (fun i => F (outputs i)) := by
  simp [aggregateSignal, map_sum]

/-- Triangle-inequality control of the population aggregate. -/
theorem norm_aggregateSignal_le (weights : ι → ℝ) (outputs : ι → S) :
    ‖aggregateSignal weights outputs‖ ≤
      ∑ i, |weights i| * ‖outputs i‖ := by
  calc
    ‖aggregateSignal weights outputs‖ ≤ ∑ i, ‖weights i • outputs i‖ := by
      exact norm_sum_le _ _
    _ = ∑ i, |weights i| * ‖outputs i‖ := by
      congr 1
      funext i
      simp [norm_smul, Real.norm_eq_abs]

/-- Nonnegative biological weights keep a finite aggregate inside a closed cone. -/
theorem aggregateSignal_mem_cone (C : ClosedCone S)
    (weights : ι → ℝ) (outputs : ι → S)
    (hweights : ∀ i, 0 ≤ weights i) (houtputs : ∀ i, outputs i ∈ C) :
    aggregateSignal weights outputs ∈ C := by
  classical
  apply C.sum_mem
  intro i hi
  exact C.smul_mem (houtputs i) (hweights i)

end Aggregation

section Filters

variable {S Z : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A deterministic temporal filter is a bounded linear operator on the signal
Hilbert space. -/
abbrev TemporalFilter := S →L[ℝ] S

/-- Every temporal filter satisfies its operator-norm bound. -/
theorem temporalFilter_norm_le (F : TemporalFilter (S := S)) (x : S) :
    ‖F x‖ ≤ ‖F‖ * ‖x‖ :=
  F.le_opNorm x

/-- An explicit sufficient condition for a filter to preserve a signal cone. -/
def PreservesCone (F : TemporalFilter (S := S)) (C : ClosedCone S) : Prop :=
  ∀ x ∈ C, F x ∈ C

/-- The closed conic image of a cone under a bounded filter. -/
def filterConeImage (F : TemporalFilter (S := S)) (C : ClosedCone S) : ClosedCone S :=
  conicHull (F '' (C : Set S))

/-- Each filtered cone element belongs to the closed conic image. -/
theorem map_mem_filterConeImage (F : TemporalFilter (S := S))
    (C : ClosedCone S) {x : S} (hx : x ∈ C) :
    F x ∈ filterConeImage F C :=
  subset_conicHull _ ⟨x, hx, rfl⟩

/-- A cone-preserving filter has no larger closed conic image. -/
theorem filterConeImage_le_of_preservesCone (F : TemporalFilter (S := S))
    (C : ClosedCone S) (hF : PreservesCone F C) :
    filterConeImage F C ≤ C := by
  apply conicHull_le
  rintro _ ⟨x, hx, rfl⟩
  exact hF x hx

/-- An operator-level transfer identity. It can represent the paper's Laplace-domain
claim once concrete transforms and gains are supplied. -/
def TransferIdentity (analysis : S →L[ℝ] Z) (filter : TemporalFilter (S := S))
    (gain : Z →L[ℝ] Z) : Prop :=
  analysis.comp filter = gain.comp analysis

/-- The operator transfer identity gives its pointwise signal identity. -/
theorem TransferIdentity.apply {analysis : S →L[ℝ] Z}
    {filter : TemporalFilter (S := S)} {gain : Z →L[ℝ] Z}
    (h : TransferIdentity analysis filter gain) (x : S) :
    analysis (filter x) = gain (analysis x) := by
  exact DFunLike.congr_fun h x

end Filters

section Dictionaries

variable {ι S : Type*} [Finite ι]
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S]

/-- The exact finite-dimensional signal subspace generated by a finite dictionary. -/
def dictionarySpan (atoms : ι → S) : Submodule ℝ S :=
  Submodule.span ℝ (Set.range atoms)

/-- A finite dictionary spans a finite-dimensional signal subspace, even when the
ambient `L²` space is infinite-dimensional. -/
theorem dictionarySpan_finiteDimensional (atoms : ι → S) :
    FiniteDimensional ℝ (dictionarySpan atoms) := by
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range atoms)

omit [Finite ι] in
/-- Filtering a finite dictionary and filtering its span produce the same algebraic
subspace. -/
theorem map_dictionarySpan (F : S →L[ℝ] S) (atoms : ι → S) :
    (dictionarySpan atoms).map F.toLinearMap =
      dictionarySpan (fun i => F (atoms i)) := by
  rw [dictionarySpan, dictionarySpan, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨atoms i, ⟨i, rfl⟩, rfl⟩

end Dictionaries

/-- Boundary conventions that lead to different finite-window convolution
operators. The paper does not choose between them. -/
inductive ConvolutionBoundary where
  | zeroExtension
  | periodic
  | causalTruncation
  deriving DecidableEq

/-- A concrete convolution interpretation must supply its kernel predicate and the
exact relation between that kernel, its boundary convention, and its bounded
operator. -/
structure ConvolutionHypotheses
    (S Kernel : Type*) [NormedAddCommGroup S] [NormedSpace ℝ S]
    (KernelSquareIntegrable : Kernel → Prop)
    (RealizesConvolution : ConvolutionBoundary → Kernel → (S →L[ℝ] S) → Prop) where
  boundary : ConvolutionBoundary
  kernel : Kernel
  operator : S →L[ℝ] S
  kernel_square_integrable : KernelSquareIntegrable kernel
  realization : RealizesConvolution boundary kernel operator

section Approximation

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- A bounded operator has finite rank when its algebraic range is finite-dimensional. -/
def IsFiniteRank (F : S →L[ℝ] S) : Prop :=
  FiniteDimensional ℝ (LinearMap.range F.toLinearMap)

/-- The exact operator-norm approximation property needed to replace a filter by
finite-rank operators. It is not inferred merely from the word "convolution". -/
def HasFiniteRankApproximations (F : S →L[ℝ] S) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : S →L[ℝ] S, IsFiniteRank R ∧ ‖F - R‖ < ε

/-- The compactness premise used by the paper's finite-rank discussion. -/
def CompactFilterPremise (F : S →L[ℝ] S) : Prop :=
  IsCompactOperator F

/-- Finite-rank bounded operators are compact. -/
theorem IsFiniteRank.compact {F : S →L[ℝ] S} (hF : IsFiniteRank F) :
    CompactFilterPremise F := by
  letI : FiniteDimensional ℝ (LinearMap.range F.toLinearMap) := hF
  have hRestricted : IsCompactOperator F.rangeRestrict :=
    isCompactOperator_of_locallyCompactSpace_dom F.rangeRestrict
  have hComposed :=
    hRestricted.clm_comp (LinearMap.range F.toLinearMap).subtypeL
  unfold CompactFilterPremise
  let rangeF := LinearMap.range F.toLinearMap
  have heq :
      ((rangeF.subtypeL : rangeF → S) ∘ (F.rangeRestrict : S → rangeF)) =
        (F : S → S) := by
    funext x
    rfl
  rw [heq] at hComposed
  exact hComposed

/-- Under the explicit compactness premise, the closure of the image of every
closed ball is compact. -/
theorem compactFilter_image_closedBall {F : S →L[ℝ] S}
    (hF : CompactFilterPremise F) (r : ℝ) :
    IsCompact (closure (F '' Metric.closedBall (0 : S) r)) :=
  hF.isCompact_closure_image_closedBall r

end Approximation

section Discretization

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The exact membrane interpolation factor appearing below equation (33). -/
def membraneUpdateFactor (Δt τ : ℝ) : ℝ :=
  1 - Real.exp (-Δt / τ)

/-- Positive time constants and nonnegative steps put the interpolation factor in
the unit interval. -/
theorem membraneUpdateFactor_mem_Icc {Δt τ : ℝ} (hΔt : 0 ≤ Δt) (hτ : 0 < τ) :
    membraneUpdateFactor Δt τ ∈ Icc 0 1 := by
  constructor
  · rw [membraneUpdateFactor, sub_nonneg, Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΔt) hτ.le
  · rw [membraneUpdateFactor, sub_le_self_iff]
    exact (Real.exp_pos _).le

/-- The first-order part of equation (33). -/
def firstOrderMembraneUpdate (lambda : ℝ) (excitation inhibition state : S) : S :=
  lambda • (excitation - inhibition) + (1 - lambda) • state

/-- Stability of the first-order update when `λ` is an interpolation weight. -/
theorem norm_firstOrderMembraneUpdate_le {lambda : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (excitation inhibition state : S) :
    ‖firstOrderMembraneUpdate lambda excitation inhibition state‖ ≤
      lambda * ‖excitation - inhibition‖ + (1 - lambda) * ‖state‖ := by
  calc
    ‖firstOrderMembraneUpdate lambda excitation inhibition state‖ ≤
        ‖lambda • (excitation - inhibition)‖ + ‖(1 - lambda) • state‖ := by
      exact norm_add_le _ _
    _ = lambda * ‖excitation - inhibition‖ + (1 - lambda) * ‖state‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hlambda0, abs_of_nonneg (sub_nonneg.mpr hlambda1)]

/-- A visible witness for the informal `O(Δt²)` in equation (33). -/
structure QuadraticRemainder (Δt : ℝ) where
  value : S
  constant : ℝ
  constant_nonnegative : 0 ≤ constant
  norm_le : ‖value‖ ≤ constant * |Δt| ^ 2

/-- Equation (33), interpreted as the exact first-order update plus an explicit
quadratically bounded remainder. -/
def membraneUpdateWithRemainder (lambda : ℝ) (excitation inhibition state : S)
    {Δt : ℝ} (remainder : QuadraticRemainder (S := S) Δt) : S :=
  firstOrderMembraneUpdate lambda excitation inhibition state + remainder.value

/-- The discretized update differs from its first-order part by exactly the supplied
remainder and hence obeys the promised quadratic error bound. -/
theorem membraneUpdate_error_le (lambda : ℝ) (excitation inhibition state : S)
    {Δt : ℝ} (remainder : QuadraticRemainder (S := S) Δt) :
    ‖membraneUpdateWithRemainder lambda excitation inhibition state remainder -
        firstOrderMembraneUpdate lambda excitation inhibition state‖ ≤
      remainder.constant * |Δt| ^ 2 := by
  simpa [membraneUpdateWithRemainder] using remainder.norm_le

end Discretization

end

end Signal
end IPNPCNS
