import RequestProject.Section31.ContinuousKernelRowsComposition
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.OpenPos

/-! A continuous kernel representing a positive operator on all L² inputs
is nonnegative everywhere under full support. Riesz-row norm bounds give
the corresponding uniform upper bound for the composed kernel. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space] (law : Measure Space)
    [IsFiniteMeasure law] [law.IsOpenPosMeasure]

theorem continuous_nonnegative_of_ae_nonnegative (function : C(Space, ℝ))
    (nonnegativeAE : ∀ᵐ point ∂law, 0 ≤ function point) : ∀ point, 0 ≤ function point := by
  have dense : Dense {point : Space | 0 ≤ function point} := law.dense_of_ae nonnegativeAE
  have closed : IsClosed {point : Space | 0 ≤ function point} :=
    isClosed_le continuous_const function.continuous
  intro point
  simpa only [closed.closure_eq, Set.mem_setOf_eq] using dense point

theorem continuousKernel_nonnegative_of_positive_L2_representation
    (kernel : Space → Space → ℝ)
    (kernelContinuous : Continuous (fun points : Space × Space => kernel points.1 points.2))
    (operator : Lp ℝ 2 law →L[ℝ] C(Space, ℝ))
    (representation : ∀ values : Lp ℝ 2 law, ∀ point,
      operator values point = ∫ other, kernel point other * values other ∂law)
    (operatorPositive : ∀ values : Lp ℝ 2 law, (∀ᵐ other ∂law, 0 ≤ values other) →
      ∀ point, 0 ≤ operator values point) :
    ∀ first second, 0 ≤ kernel first second := by
  intro first
  let slice : C(Space, ℝ) := ⟨kernel first,
    kernelContinuous.comp (continuous_const.prodMk continuous_id)⟩
  have sliceIntegrable : Integrable slice law := by
    apply Integrable.of_bound slice.continuous.measurable.aestronglyMeasurable ‖slice‖
    exact Eventually.of_forall fun point => slice.norm_coe_le_norm point
  have sliceNonnegative : ∀ᵐ second ∂law, 0 ≤ slice second := by
    apply ae_nonneg_of_forall_setIntegral_nonneg sliceIntegrable
    intro region regionMeasurable regionFinite
    let test := indicatorConstLp 2 regionMeasurable regionFinite.ne (1 : ℝ)
    have testAE := indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
      (hs := regionMeasurable) (hμs := regionFinite.ne) (c := (1 : ℝ))
    have testNonnegative : ∀ᵐ point ∂law, 0 ≤ test point := by
      filter_upwards [testAE] with point equality
      rw [equality]
      by_cases membership : point ∈ region <;> simp [Set.indicator, membership]
    have testIntegral : (∫ other, kernel first other * test other ∂law) =
        ∫ other in region, slice other ∂law := by
      calc
        _ = ∫ other, region.indicator slice other ∂law := by
          apply integral_congr_ae
          filter_upwards [testAE] with other equality
          rw [equality]
          by_cases membership : other ∈ region <;> simp [Set.indicator, membership, slice]
        _ = _ := integral_indicator regionMeasurable
    have nonnegative := operatorPositive test testNonnegative first
    rw [representation, testIntegral] at nonnegative
    exact nonnegative
  exact continuous_nonnegative_of_ae_nonnegative law slice sliceNonnegative

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    [CompleteSpace Hilbert]

theorem continuousOperatorKernelRow_norm_le
    (operator : Hilbert →L[ℝ] C(Space, ℝ)) (point : Space) :
    ‖continuousOperatorKernelRow operator point‖ ≤ ‖operator‖ := by
  have squaredIdentity : ‖continuousOperatorKernelRow operator point‖ ^ 2 =
      operator (continuousOperatorKernelRow operator point) point := by
    rw [continuousOperatorKernelRow_represents, real_inner_self_eq_norm_sq]
  have squaredBound : ‖continuousOperatorKernelRow operator point‖ ^ 2 ≤
      ‖operator‖ * ‖continuousOperatorKernelRow operator point‖ := by
    rw [squaredIdentity]
    exact (le_abs_self _).trans
      (((operator (continuousOperatorKernelRow operator point)).norm_coe_le_norm point).trans
        (operator.le_opNorm _))
  by_cases rowZero : ‖continuousOperatorKernelRow operator point‖ = 0
  · rw [rowZero]
    exact norm_nonneg operator
  · have rowPositive := lt_of_le_of_ne (norm_nonneg (continuousOperatorKernelRow operator point)) (Ne.symm rowZero)
    nlinarith

theorem continuousOperatorComposedKernel_abs_le
    (operator : Lp ℝ 2 law →L[ℝ] C(Space, ℝ)) (first second : Space) :
    |continuousOperatorComposedKernel law operator first second| ≤ ‖operator‖ ^ 2 := by
  calc
    _ ≤ ‖continuousOperatorKernelRow operator first‖ * ‖continuousOperatorKernelRow operator second‖ := by
      simpa only [continuousOperatorComposedKernel, Real.norm_eq_abs] using
        norm_inner_le_norm (𝕜 := ℝ) (continuousOperatorKernelRow operator first) (continuousOperatorKernelRow operator second)
    _ ≤ ‖operator‖ * ‖operator‖ :=
      mul_le_mul (continuousOperatorKernelRow_norm_le operator first)
        (continuousOperatorKernelRow_norm_le operator second)
        (norm_nonneg (continuousOperatorKernelRow operator second)) (norm_nonneg operator)
    _ = _ := (pow_two _).symm

end
end IGS.Sec31

#print axioms IGS.Sec31.continuous_nonnegative_of_ae_nonnegative
#print axioms IGS.Sec31.continuousKernel_nonnegative_of_positive_L2_representation
#print axioms IGS.Sec31.continuousOperatorKernelRow_norm_le
#print axioms IGS.Sec31.continuousOperatorComposedKernel_abs_le
