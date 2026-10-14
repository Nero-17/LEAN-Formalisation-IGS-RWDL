import RequestProject.Section31.ContinuousKernelFixedWindow
import RequestProject.Section31.QuadraticEnergySemigroupSymmetry

/-! Identify any continuous density of the actual closed semigroup with
the diagonal from a compact half-time lift. This is equality of kernels,
not only almost-everywhere equality of their associated operators. -/

namespace IGS.Sec31

open MeasureTheory
open scoped NNReal
noncomputable section
set_option maxHeartbeats 1000000

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space] (law : Measure Space)
    [IsFiniteMeasure law] [law.IsOpenPosMeasure]

theorem continuousKernel_diagonal_eq_half_time_row
    (domain : Submodule ℝ (Lp ℝ 2 law)) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values)
    (closable : QuadraticEnergySpace.SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set (Lp ℝ 2 law)))
    (embedding : C(Space, ℝ) →L[ℝ] Lp ℝ 2 law)
    (embeddingInjective : Function.Injective embedding)
    (embeddingAE : ∀ representative : C(Space, ℝ),
      (embedding representative : Space → ℝ) =ᵐ[law] representative)
    (time : ℝ≥0)
    (halfLift fullLift : Lp ℝ 2 law →L[ℝ] C(Space, ℝ))
    (halfCompact : IsCompactOperator halfLift)
    (halfCompatibility : ∀ forcing, embedding (halfLift forcing) =
      QuadraticEnergySpace.closedSemigroup domain form nonnegative closable domainDense (time / 2) forcing)
    (fullCompatibility : ∀ forcing, embedding (fullLift forcing) =
      QuadraticEnergySpace.closedSemigroup domain form nonnegative closable domainDense time forcing)
    (kernel : Space → Space → ℝ)
    (kernelContinuous : Continuous (fun points : Space × Space => kernel points.1 points.2))
    (representation : ∀ forcing point, fullLift forcing point =
      ∫ other, kernel point other * forcing other ∂law) (point : Space) :
    kernel point point = ‖continuousOperatorKernelRow halfLift point‖ ^ 2 := by
  have halfAdd : time / 2 + time / 2 = time := by
    apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat]
    ring
  have liftedComposition (forcing : Lp ℝ 2 law) :
      halfLift (QuadraticEnergySpace.closedSemigroup domain form nonnegative closable domainDense
        (time / 2) forcing) = fullLift forcing := by
    apply embeddingInjective
    rw [halfCompatibility, fullCompatibility,
      ← ContinuousLinearMap.comp_apply, ← QuadraticEnergySpace.closedSemigroup_add, halfAdd]
  have fixedInputContinuous : Continuous (fun other : Space => (point, other)) :=
    continuous_const.prodMk continuous_id
  have kernelSliceContinuous : Continuous (kernel point) :=
    kernelContinuous.comp fixedInputContinuous
  have composedContinuous : Continuous (fun points : Space × Space =>
      continuousOperatorComposedKernel law halfLift points.1 points.2) :=
    continuousOperatorComposedKernel_continuous law halfLift halfCompact
  have composedSliceContinuous : Continuous (continuousOperatorComposedKernel law halfLift point) :=
    composedContinuous.comp fixedInputContinuous
  let kernelSlice : C(Space, ℝ) := ⟨kernel point, kernelSliceContinuous⟩
  let composedSlice : C(Space, ℝ) := ⟨continuousOperatorComposedKernel law halfLift point,
    composedSliceContinuous⟩
  have rowEquality : kernelSlice = composedSlice := by
    apply continuous_L2_kernel_row_unique law kernelSlice composedSlice
    intro forcing
    change (∫ other, kernel point other * forcing other ∂law) =
      ∫ other, continuousOperatorComposedKernel law halfLift point other * forcing other ∂law
    rw [← representation]
    have equality := continuousOperatorComposedKernel_integral law embedding embeddingAE halfLift
      (QuadraticEnergySpace.closedSemigroup domain form nonnegative closable domainDense (time / 2))
      (QuadraticEnergySpace.closedSemigroup_selfAdjoint domain form nonnegative closable domainDense (time / 2))
      halfCompatibility point forcing
    rw [liftedComposition] at equality
    exact equality
  have diagonalEquality := congrArg (fun function : C(Space, ℝ) => function point) rowEquality
  simpa only [kernelSlice, composedSlice, ContinuousMap.coe_mk,
    continuousOperatorComposedKernel, real_inner_self_eq_norm_sq] using diagonalEquality

end
end IGS.Sec31

#print axioms IGS.Sec31.continuousKernel_diagonal_eq_half_time_row
