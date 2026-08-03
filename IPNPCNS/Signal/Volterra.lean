import IPNPCNS.Signal.Deterministic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.InnerProductSpace.LinearMap

open MeasureTheory Set
open scoped ENNReal MeasureTheory symmDiff

/-!
# Compact causal convolution on a finite window

This file constructs the causal unit-step convolution operator on the scalar signal
space over `[0, T]`.  The operator is the Volterra prefix integral

`(V x)(t) = ∫ s in (0, t], x(s)`.

It is represented by the `L²` path of prefix indicators.  General lemmas first turn
an `L²` path of Hilbert-space vectors into a bounded analysis operator.  Simple
functions then provide finite-rank approximants in operator norm, which proves
compactness.  The final section instantiates `ConvolutionHypotheses` with the
explicit `.causalTruncation` convention; periodic and zero-extension semantics are
not identified with this operator.
-/

noncomputable section

namespace IPNPCNS.Signal

variable {X H : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def kernelAnalysisOperator (k : Lp H 2 μ) : H →L[ℝ] Lp ℝ 2 μ :=
  (((innerSL ℝ).holderL μ 2 ∞ 2) k).comp (Lp.constL ∞ μ ℝ)

lemma kernelAnalysisOperator_apply (k : Lp H 2 μ) (x : H) :
    kernelAnalysisOperator μ k x =
      (innerSL ℝ).holder 2 k (Lp.const ∞ μ x) := rfl

lemma kernelAnalysisOperator_apply_ae (k : Lp H 2 μ) (x : H) :
    kernelAnalysisOperator μ k x =ᵐ[μ]
      fun t => inner ℝ (k t) x := by
  rw [kernelAnalysisOperator_apply]
  filter_upwards [(innerSL ℝ).coeFn_holder (r := (2 : ℝ≥0∞)) k (Lp.const ∞ μ x),
    Lp.coeFn_const (μ := μ) (p := ∞) x] with t hholder hconst
  rw [hholder, hconst]
  rfl

omit [InnerProductSpace ℝ H] in
lemma norm_const_top_le (x : H) :
    ‖Lp.const ∞ μ x‖ ≤ ‖x‖ := by
  simpa using (Lp.norm_const_le (μ := μ) (p := ∞) x)

lemma norm_kernelAnalysisOperator_apply_le (k : Lp H 2 μ) (x : H) :
    ‖kernelAnalysisOperator μ k x‖ ≤ ‖k‖ * ‖x‖ := by
  rw [kernelAnalysisOperator_apply]
  calc
    ‖(innerSL ℝ).holder 2 k (Lp.const ∞ μ x)‖ ≤
        ‖innerSL ℝ‖ * ‖k‖ * ‖Lp.const ∞ μ x‖ :=
      ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
    _ ≤ ‖innerSL ℝ‖ * ‖k‖ * ‖x‖ := by
      exact mul_le_mul_of_nonneg_left (norm_const_top_le μ x)
        (mul_nonneg (norm_nonneg (innerSL ℝ (E := H))) (norm_nonneg k))
    _ ≤ 1 * ‖k‖ * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (norm_innerSL_le ℝ (E := H)) (norm_nonneg k))
        (norm_nonneg x)
    _ = ‖k‖ * ‖x‖ := by ring

lemma norm_kernelAnalysisOperator_le (k : Lp H 2 μ) :
    ‖kernelAnalysisOperator μ k‖ ≤ ‖k‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg k)
  intro x
  exact norm_kernelAnalysisOperator_apply_le μ k x

lemma kernelAnalysisOperator_add (k l : Lp H 2 μ) :
    kernelAnalysisOperator μ (k + l) =
      kernelAnalysisOperator μ k + kernelAnalysisOperator μ l := by
  ext x
  simp [kernelAnalysisOperator]

lemma kernelAnalysisOperator_smul (a : ℝ) (k : Lp H 2 μ) :
    kernelAnalysisOperator μ (a • k) = a • kernelAnalysisOperator μ k := by
  ext x
  simp [kernelAnalysisOperator]

lemma kernelAnalysisOperator_sub (k l : Lp H 2 μ) :
    kernelAnalysisOperator μ (k - l) =
      kernelAnalysisOperator μ k - kernelAnalysisOperator μ l := by
  ext x
  simp [kernelAnalysisOperator]

lemma norm_kernelAnalysisOperator_sub_le (k l : Lp H 2 μ) :
    ‖kernelAnalysisOperator μ k - kernelAnalysisOperator μ l‖ ≤ ‖k - l‖ := by
  rw [← kernelAnalysisOperator_sub]
  exact norm_kernelAnalysisOperator_le μ (k - l)

omit [IsFiniteMeasure μ] in
lemma isFiniteRank_rankOne (u v : Lp ℝ 2 μ) :
    IPNPCNS.Signal.IsFiniteRank (InnerProductSpace.rankOne ℝ u v) := by
  letI : FiniteDimensional ℝ (ℝ ∙ u) := inferInstance
  apply Submodule.finiteDimensional_of_le (S₂ := ℝ ∙ u)
  rintro y ⟨x, rfl⟩
  change inner ℝ v x • u ∈ ℝ ∙ u
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)

omit [IsFiniteMeasure μ] in
lemma isFiniteRank_add {F G : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ}
    (hF : IPNPCNS.Signal.IsFiniteRank F)
    (hG : IPNPCNS.Signal.IsFiniteRank G) :
    IPNPCNS.Signal.IsFiniteRank (F + G) := by
  letI : FiniteDimensional ℝ (LinearMap.range F.toLinearMap) := hF
  letI : FiniteDimensional ℝ (LinearMap.range G.toLinearMap) := hG
  apply Submodule.finiteDimensional_of_le
    (S₂ := LinearMap.range F.toLinearMap ⊔ LinearMap.range G.toLinearMap)
  simpa using LinearMap.range_add_le F.toLinearMap G.toLinearMap

lemma kernelAnalysisOperator_indicatorConst
    (c : H) {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    kernelAnalysisOperator μ (indicatorConstLp 2 hs hμs c) =
      InnerProductSpace.rankOne ℝ (indicatorConstLp 2 hs hμs (1 : ℝ)) c := by
  ext x
  rw [InnerProductSpace.rankOne_apply]
  filter_upwards [kernelAnalysisOperator_apply_ae μ
      (indicatorConstLp 2 hs hμs c) x,
    (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs)
      (hμs := hμs) (c := c)),
    (indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs)
      (hμs := hμs) (c := (1 : ℝ))),
    Lp.coeFn_smul (inner ℝ c x) (indicatorConstLp 2 hs hμs (1 : ℝ))]
      with t hleft hkernel hout hsmul
  rw [hleft, hkernel, hsmul]
  change inner ℝ (s.indicator (fun _ => c) t) x =
    inner ℝ c x * (indicatorConstLp 2 hs hμs (1 : ℝ)) t
  rw [hout]
  by_cases ht : t ∈ s <;> simp [Set.indicator, ht]

lemma kernelAnalysisOperator_indicatorConst_finiteRank
    (c : Lp ℝ 2 μ) {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    IPNPCNS.Signal.IsFiniteRank
      (kernelAnalysisOperator μ (indicatorConstLp 2 hs hμs c)) := by
  rw [kernelAnalysisOperator_indicatorConst]
  exact isFiniteRank_rankOne μ _ _

lemma kernelAnalysisOperator_simple_finiteRank
    (f : Lp.simpleFunc (Lp ℝ 2 μ) 2 μ) :
    IPNPCNS.Signal.IsFiniteRank
      (kernelAnalysisOperator μ (f : Lp (Lp ℝ 2 μ) 2 μ)) := by
  let P : Lp.simpleFunc (Lp ℝ 2 μ) 2 μ → Prop := fun g =>
    IPNPCNS.Signal.IsFiniteRank
      (kernelAnalysisOperator μ (g : Lp (Lp ℝ 2 μ) 2 μ))
  change P f
  refine Lp.simpleFunc.induction (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    (P := P) ?_ ?_ f
  · intro c s hs hμs
    simpa only [P, Lp.simpleFunc.coe_indicatorConst] using
      kernelAnalysisOperator_indicatorConst_finiteRank μ c hs hμs.ne
  · intro f g hf hg _hdisjoint hF hG
    dsimp only [P] at hF hG ⊢
    rw [show ((SimpleFunc.toLp f hf + SimpleFunc.toLp g hg :
        Lp.simpleFunc (Lp ℝ 2 μ) 2 μ) : Lp (Lp ℝ 2 μ) 2 μ) =
          (SimpleFunc.toLp f hf : Lp (Lp ℝ 2 μ) 2 μ) +
            (SimpleFunc.toLp g hg : Lp (Lp ℝ 2 μ) 2 μ) by rfl,
      kernelAnalysisOperator_add]
    exact isFiniteRank_add μ hF hG

theorem kernelAnalysisOperator_hasFiniteRankApproximations
    (k : Lp (Lp ℝ 2 μ) 2 μ) :
    IPNPCNS.Signal.HasFiniteRankApproximations
      (kernelAnalysisOperator μ k) := by
  intro ε hε
  obtain ⟨f, hf⟩ :=
    (Lp.simpleFunc.denseRange (E := Lp ℝ 2 μ) (μ := μ)
      (p := (2 : ℝ≥0∞)) (by norm_num)).exists_dist_lt k hε
  refine ⟨kernelAnalysisOperator μ (f : Lp (Lp ℝ 2 μ) 2 μ),
    kernelAnalysisOperator_simple_finiteRank μ f, ?_⟩
  calc
    ‖kernelAnalysisOperator μ k -
        kernelAnalysisOperator μ (f : Lp (Lp ℝ 2 μ) 2 μ)‖ ≤
        ‖k - (f : Lp (Lp ℝ 2 μ) 2 μ)‖ :=
      norm_kernelAnalysisOperator_sub_le μ _ _
    _ = dist k (f : Lp (Lp ℝ 2 μ) 2 μ) := by
      rw [dist_eq_norm]
    _ < ε := hf

omit [IsFiniteMeasure μ] in
lemma hasFiniteRankApproximations_compact
    {F : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ}
    (hF : IPNPCNS.Signal.HasFiniteRankApproximations F) :
    IPNPCNS.Signal.CompactFilterPremise F := by
  have hmem : F ∈ closure {R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ |
      IsCompactOperator R} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨R, hR, hclose⟩ := hF ε hε
    refine ⟨R, hR.compact, ?_⟩
    simpa [dist_eq_norm, norm_sub_rev] using hclose
  rw [isClosed_setOf_isCompactOperator.closure_eq] at hmem
  exact hmem

theorem kernelAnalysisOperator_compact
    (k : Lp (Lp ℝ 2 μ) 2 μ) :
    IPNPCNS.Signal.CompactFilterPremise (kernelAnalysisOperator μ k) :=
  hasFiniteRankApproximations_compact μ
    (kernelAnalysisOperator_hasFiniteRankApproximations μ k)

section Prefix

def clipToWindow (T t : ℝ) : ℝ := max 0 (min t T)

lemma clipToWindow_nonneg (T t : ℝ) : 0 ≤ clipToWindow T t := by
  simp [clipToWindow]

lemma clipToWindow_le {T t : ℝ} (hT : 0 ≤ T) : clipToWindow T t ≤ T := by
  simp [clipToWindow, hT]

lemma clipToWindow_eq_self {T t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    clipToWindow T t = t := by
  simp [clipToWindow, ht.1, ht.2]

lemma continuous_clipToWindow (T : ℝ) : Continuous (clipToWindow T) := by
  unfold clipToWindow
  fun_prop

def prefixSet (T t : ℝ) : Set ℝ :=
  Set.Ioc 0 (clipToWindow T t)

lemma measurableSet_prefixSet (T t : ℝ) : MeasurableSet (prefixSet T t) :=
  measurableSet_Ioc

lemma prefixSet_subset_window {T t : ℝ} (hT : 0 ≤ T) :
    prefixSet T t ⊆ Set.Icc (0 : ℝ) T := by
  intro s hs
  rw [prefixSet, Set.mem_Ioc] at hs
  exact ⟨hs.1.le, hs.2.trans (clipToWindow_le hT)⟩

lemma prefixSet_symmDiff (T a b : ℝ) :
    prefixSet T a ∆ prefixSet T b =
      Set.uIoc (clipToWindow T a) (clipToWindow T b) := by
  ext s
  simp only [prefixSet, Set.mem_symmDiff, Set.mem_Ioc, Set.mem_uIoc]
  have ha := clipToWindow_nonneg T a
  have hb := clipToWindow_nonneg T b
  grind

lemma recordingMeasure_prefixSet_symmDiff {T a b : ℝ} (hT : 0 ≤ T) :
    IPNPCNS.Signal.recordingMeasure T (prefixSet T a ∆ prefixSet T b) =
      ENNReal.ofReal |clipToWindow T b - clipToWindow T a| := by
  rw [prefixSet_symmDiff, IPNPCNS.Signal.recordingMeasure,
    Measure.restrict_apply measurableSet_uIoc]
  have hsubset : Set.uIoc (clipToWindow T a) (clipToWindow T b) ⊆
      Set.Icc (0 : ℝ) T := by
    rw [← prefixSet_symmDiff]
    exact Set.symmDiff_subset_union.trans
      (Set.union_subset (prefixSet_subset_window hT) (prefixSet_subset_window hT))
  rw [Set.inter_eq_left.2 hsubset, Real.volume_uIoc]

local instance recordingMeasure_isFiniteMeasure (T : ℝ) :
    IsFiniteMeasure (IPNPCNS.Signal.recordingMeasure T) := ⟨by simp⟩

def prefixVector (T t : ℝ) : IPNPCNS.Signal.ScalarSignal T :=
  indicatorConstLp 2 (measurableSet_prefixSet T t)
    (measure_ne_top _ _) (1 : ℝ)

lemma prefixVector_continuous {T : ℝ} (hT : 0 ≤ T) :
    Continuous (prefixVector T) := by
  apply continuous_indicatorConstLp_set (p := (2 : ℝ≥0∞)) (by norm_num)
  intro t
  rw [show (fun u => IPNPCNS.Signal.recordingMeasure T
      (prefixSet T u ∆ prefixSet T t)) =
        fun u => ENNReal.ofReal |clipToWindow T t - clipToWindow T u| by
    funext u
    exact recordingMeasure_prefixSet_symmDiff hT]
  have hcont : Continuous
      (fun u => ENNReal.ofReal |clipToWindow T t - clipToWindow T u|) :=
    ENNReal.continuous_ofReal.comp
      (continuous_abs.comp (continuous_const.sub (continuous_clipToWindow T)))
  simpa using hcont.tendsto t

lemma recordingMeasure_prefixSet {T t : ℝ} (hT : 0 ≤ T) :
    IPNPCNS.Signal.recordingMeasure T (prefixSet T t) =
      ENNReal.ofReal (clipToWindow T t) := by
  rw [IPNPCNS.Signal.recordingMeasure,
    Measure.restrict_apply (measurableSet_prefixSet T t),
    Set.inter_eq_left.2 (prefixSet_subset_window hT), prefixSet,
    Real.volume_Ioc]
  simp

lemma prefixVector_norm_sq {T t : ℝ} (hT : 0 ≤ T) :
    ‖prefixVector T t‖ ^ 2 = clipToWindow T t := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [prefixVector]
  rw [L2.real_inner_indicatorConstLp_one_indicatorConstLp_one,
    Set.inter_self, Measure.real, recordingMeasure_prefixSet hT,
    ENNReal.toReal_ofReal (clipToWindow_nonneg T t)]

lemma norm_prefixVector_le_sqrt {T t : ℝ} (hT : 0 ≤ T) :
    ‖prefixVector T t‖ ≤ Real.sqrt T := by
  have hnorm := prefixVector_norm_sq (t := t) hT
  have hclip := clipToWindow_le (t := t) hT
  have hsqrt := Real.sq_sqrt hT
  nlinarith [norm_nonneg (prefixVector T t), Real.sqrt_nonneg T]

private lemma prefixVector_memLp {T : ℝ} (hT : 0 ≤ T) :
    MemLp (prefixVector T) 2 (IPNPCNS.Signal.recordingMeasure T) := by
  apply MemLp.of_bound (prefixVector_continuous hT).aestronglyMeasurable (Real.sqrt T)
  exact Filter.Eventually.of_forall fun t => norm_prefixVector_le_sqrt hT

def prefixKernel (T : ℝ) (hT : 0 ≤ T) :
    Lp (IPNPCNS.Signal.ScalarSignal T) 2
      (IPNPCNS.Signal.recordingMeasure T) :=
  (prefixVector_memLp hT).toLp (prefixVector T)

lemma prefixKernel_apply_ae (T : ℝ) (hT : 0 ≤ T) :
    prefixKernel T hT =ᵐ[IPNPCNS.Signal.recordingMeasure T] prefixVector T :=
  (prefixVector_memLp hT).coeFn_toLp

lemma norm_prefixKernel_le {T : ℝ} (hT : 0 ≤ T) :
    ‖prefixKernel T hT‖ ≤ T := by
  rw [prefixKernel, Lp.norm_toLp]
  have hbound :
      eLpNorm (prefixVector T) 2 (IPNPCNS.Signal.recordingMeasure T) ≤
        IPNPCNS.Signal.recordingMeasure T Set.univ ^
            (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (Real.sqrt T) :=
    eLpNorm_le_of_ae_bound
      (Filter.Eventually.of_forall fun t => norm_prefixVector_le_sqrt hT)
  rw [IPNPCNS.Signal.recordingMeasure_univ] at hbound
  calc
    ENNReal.toReal
        (eLpNorm (prefixVector T) 2 (IPNPCNS.Signal.recordingMeasure T)) ≤
        ENNReal.toReal
          (ENNReal.ofReal T ^ (2 : ℝ≥0∞).toReal⁻¹ *
            ENNReal.ofReal (Real.sqrt T)) := by
      exact ENNReal.toReal_mono (by finiteness) hbound
    _ = T := by
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal hT,
        ENNReal.toReal_ofReal (Real.sqrt_nonneg T)]
      norm_num
      rw [← Real.sqrt_eq_rpow, ← pow_two, Real.sq_sqrt hT]

/-- The causal Volterra integration operator on the recording window. -/
def volterraOperator (T : ℝ) (hT : 0 ≤ T) :
    IPNPCNS.Signal.ScalarSignal T →L[ℝ] IPNPCNS.Signal.ScalarSignal T :=
  kernelAnalysisOperator (IPNPCNS.Signal.recordingMeasure T) (prefixKernel T hT)

lemma volterra_apply_inner_ae (T : ℝ) (hT : 0 ≤ T)
    (x : IPNPCNS.Signal.ScalarSignal T) :
    volterraOperator T hT x =ᵐ[IPNPCNS.Signal.recordingMeasure T]
      fun t => inner ℝ (prefixVector T t) x := by
  filter_upwards [kernelAnalysisOperator_apply_ae
      (IPNPCNS.Signal.recordingMeasure T) (prefixKernel T hT) x,
    prefixKernel_apply_ae T hT] with t hop hkernel
  exact hop.trans (congrArg (fun k => inner ℝ k x) hkernel)

lemma prefixVector_inner_eq_setIntegral (T t : ℝ)
    (x : IPNPCNS.Signal.ScalarSignal T) :
    inner ℝ (prefixVector T t) x =
      ∫ s in prefixSet T t, x s ∂IPNPCNS.Signal.recordingMeasure T := by
  simpa only [prefixVector] using
    L2.inner_indicatorConstLp_one (measurableSet_prefixSet T t)
      (measure_ne_top (IPNPCNS.Signal.recordingMeasure T) (prefixSet T t)) x

/-- Almost-everywhere causal integral formula, with clipping outside the window. -/
theorem volterra_apply_clippedIntegral_ae (T : ℝ) (hT : 0 ≤ T)
    (x : IPNPCNS.Signal.ScalarSignal T) :
    volterraOperator T hT x =ᵐ[IPNPCNS.Signal.recordingMeasure T]
      fun t => ∫ s in Set.Ioc 0 (clipToWindow T t), x s
        ∂IPNPCNS.Signal.recordingMeasure T := by
  filter_upwards [volterra_apply_inner_ae T hT x] with t ht
  rw [ht, prefixVector_inner_eq_setIntegral, prefixSet]

/-- On the recording window, the clipped formula is the usual causal prefix integral. -/
theorem volterra_apply_integral_ae (T : ℝ) (hT : 0 ≤ T)
    (x : IPNPCNS.Signal.ScalarSignal T) :
    volterraOperator T hT x =ᵐ[IPNPCNS.Signal.recordingMeasure T]
      fun t => ∫ s in Set.Ioc 0 t, x s ∂IPNPCNS.Signal.recordingMeasure T := by
  filter_upwards [volterra_apply_clippedIntegral_ae T hT x,
    show ∀ᵐ t ∂IPNPCNS.Signal.recordingMeasure T, t ∈ Set.Icc (0 : ℝ) T by
      simpa only [IPNPCNS.Signal.recordingMeasure] using
        ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht hwindow
  simpa only [clipToWindow_eq_self hwindow] using ht

theorem norm_volterraOperator_le {T : ℝ} (hT : 0 ≤ T) :
    ‖volterraOperator T hT‖ ≤ T := by
  exact (norm_kernelAnalysisOperator_le
    (IPNPCNS.Signal.recordingMeasure T) (prefixKernel T hT)).trans
      (norm_prefixKernel_le hT)

theorem volterra_hasFiniteRankApproximations (T : ℝ) (hT : 0 ≤ T) :
    IPNPCNS.Signal.HasFiniteRankApproximations (volterraOperator T hT) :=
  kernelAnalysisOperator_hasFiniteRankApproximations
    (IPNPCNS.Signal.recordingMeasure T) (prefixKernel T hT)

theorem volterra_compact (T : ℝ) (hT : 0 ≤ T) :
    IPNPCNS.Signal.CompactFilterPremise (volterraOperator T hT) :=
  kernelAnalysisOperator_compact
    (IPNPCNS.Signal.recordingMeasure T) (prefixKernel T hT)

theorem volterra_map_add (T : ℝ) (hT : 0 ≤ T)
    (x y : IPNPCNS.Signal.ScalarSignal T) :
    volterraOperator T hT (x + y) =
      volterraOperator T hT x + volterraOperator T hT y :=
  map_add (volterraOperator T hT) x y

theorem volterra_map_smul (T : ℝ) (hT : 0 ≤ T) (a : ℝ)
    (x : IPNPCNS.Signal.ScalarSignal T) :
    volterraOperator T hT (a • x) = a • volterraOperator T hT x :=
  map_smul (volterraOperator T hT) a x

/-- The causal unit-step impulse response. -/
def unitStepImpulse (u : ℝ) : ℝ :=
  Set.Ici (0 : ℝ) |>.indicator (fun _ => 1) u

lemma unitStepImpulse_measurable : Measurable unitStepImpulse := by
  exact measurable_const.indicator measurableSet_Ici

lemma norm_unitStepImpulse_le_one (u : ℝ) : ‖unitStepImpulse u‖ ≤ 1 := by
  by_cases hu : 0 ≤ u <;> simp [unitStepImpulse, hu]

/-- Square-integrability means `L²` membership on the selected finite recording window. -/
def KernelSquareIntegrable (T : ℝ) (kernel : ℝ → ℝ) : Prop :=
  MemLp kernel 2 (IPNPCNS.Signal.recordingMeasure T)

lemma unitStepImpulse_squareIntegrable (T : ℝ) :
    KernelSquareIntegrable T unitStepImpulse := by
  apply MemLp.of_bound unitStepImpulse_measurable.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall norm_unitStepImpulse_le_one

/-- Exact semantics of causal, finite-window convolution used in this construction. -/
def RealizesCausalConvolution (T : ℝ)
    (boundary : IPNPCNS.Signal.ConvolutionBoundary) (kernel : ℝ → ℝ)
    (F : IPNPCNS.Signal.ScalarSignal T →L[ℝ]
      IPNPCNS.Signal.ScalarSignal T) : Prop :=
  boundary = .causalTruncation ∧
    ∀ x, F x =ᵐ[IPNPCNS.Signal.recordingMeasure T]
      fun t => ∫ s in Set.Ioc 0 t, kernel (t - s) * x s
        ∂IPNPCNS.Signal.recordingMeasure T

lemma volterra_realizes_unitStepConvolution (T : ℝ) (hT : 0 ≤ T) :
    RealizesCausalConvolution T .causalTruncation unitStepImpulse
      (volterraOperator T hT) := by
  refine ⟨rfl, fun x => ?_⟩
  filter_upwards [volterra_apply_integral_ae T hT x] with t hv
  rw [hv]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem
      (μ := IPNPCNS.Signal.recordingMeasure T) measurableSet_Ioc] with s hs
  have hdiff : 0 ≤ t - s := sub_nonneg.mpr hs.2
  simp [unitStepImpulse, hdiff]

/-- T-0014's convolution package, now inhabited by a proved concrete model. -/
def unitStepConvolutionHypotheses (T : ℝ) (hT : 0 ≤ T) :
    IPNPCNS.Signal.ConvolutionHypotheses
      (IPNPCNS.Signal.ScalarSignal T) (ℝ → ℝ)
      (KernelSquareIntegrable T) (RealizesCausalConvolution T) where
  boundary := .causalTruncation
  kernel := unitStepImpulse
  operator := volterraOperator T hT
  kernel_square_integrable := unitStepImpulse_squareIntegrable T
  realization := volterra_realizes_unitStepConvolution T hT

theorem unitStepConvolution_hasFiniteRankApproximations (T : ℝ) (hT : 0 ≤ T) :
    IPNPCNS.Signal.HasFiniteRankApproximations
      (unitStepConvolutionHypotheses T hT).operator :=
  volterra_hasFiniteRankApproximations T hT

theorem unitStepConvolution_compact (T : ℝ) (hT : 0 ≤ T) :
    IPNPCNS.Signal.CompactFilterPremise
      (unitStepConvolutionHypotheses T hT).operator :=
  volterra_compact T hT

theorem unitStepConvolution_boundary (T : ℝ) (hT : 0 ≤ T) :
    (unitStepConvolutionHypotheses T hT).boundary = .causalTruncation := rfl

theorem unitStepConvolution_not_periodic (T : ℝ) (hT : 0 ≤ T) :
    ¬ RealizesCausalConvolution T .periodic unitStepImpulse
      (unitStepConvolutionHypotheses T hT).operator := by
  intro h
  exact IPNPCNS.Signal.ConvolutionBoundary.noConfusion h.1

theorem unitStepConvolution_not_zeroExtension (T : ℝ) (hT : 0 ≤ T) :
    ¬ RealizesCausalConvolution T .zeroExtension unitStepImpulse
      (unitStepConvolutionHypotheses T hT).operator := by
  intro h
  exact IPNPCNS.Signal.ConvolutionBoundary.noConfusion h.1

end Prefix

end IPNPCNS.Signal
