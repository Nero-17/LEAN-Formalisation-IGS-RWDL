import RequestProject.Section31.MarkovKernelIntegralInvariance
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Extending the actual kernel representation through uniformly bounded
continuous approximations. Measure invariance transfers the input AE limit
to almost every transition measure; dominated convergence then identifies
the actual output. No kernel representation for arbitrary inputs is assumed. -/

namespace IGS.Sec31.CountableMarkov

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ProbabilityTheory

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    (measure : Measure X) [IsFiniteMeasure measure]

theorem ae_kernel_integral_of_bounded_test_limits
    (operator : C(X, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (kernel : Kernel X X) [IsMarkovKernel kernel] (invariant : kernel.Invariant measure)
    (representation : ∀ values : C(X, ℝ), ∀ᵐ point ∂measure,
      (∫ location, values location ∂kernel point) = operator values point)
    (sequence : ℕ → C(X, ℝ)) (input output : X → ℝ) (bound : ℝ)
    (bounded : ∀ index location, ‖sequence index location‖ ≤ bound)
    (inputLimit : ∀ᵐ location ∂measure,
      Tendsto (fun index => sequence index location) atTop (nhds (input location)))
    (outputLimit : ∀ᵐ point ∂measure,
      Tendsto (fun index => operator (sequence index) point) atTop (nhds (output point))) :
    ∀ᵐ point ∂measure, (∫ location, input location ∂kernel point) = output point := by
  have inputLimitComposed : ∀ᵐ location ∂(kernel ∘ₘ measure),
      Tendsto (fun index => sequence index location) atTop (nhds (input location)) := by
    simpa only [invariant.def] using inputLimit
  have inputLimits := Measure.ae_ae_of_ae_comp inputLimitComposed
  have identities : ∀ᵐ point ∂measure, ∀ index : ℕ,
      (∫ location, sequence index location ∂kernel point) = operator (sequence index) point :=
    ae_all_iff.mpr (fun index => representation (sequence index))
  filter_upwards [inputLimits, identities, outputLimit] with point limit identities pointOutputLimit
  have integralLimit : Tendsto (fun index => ∫ location, sequence index location ∂kernel point)
      atTop (nhds (∫ location, input location ∂kernel point)) :=
    tendsto_integral_of_dominated_convergence (fun _ => bound)
      (fun index => (sequence index).continuous.measurable.aestronglyMeasurable)
      (integrable_const bound)
      (fun index => Eventually.of_forall (bounded index)) limit
  have identifiedOutput : Tendsto (fun index => ∫ location, sequence index location ∂kernel point)
      atTop (nhds (output point)) := by
    simpa only [identities] using pointOutputLimit
  exact tendsto_nhds_unique integralLimit identifiedOutput

theorem ae_kernel_integral_of_bounded_continuous_L2_approximation
    (semigroup : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (kernel : Kernel X X) [IsMarkovKernel kernel] (invariant : kernel.Invariant measure)
    (representation : ∀ values : C(X, ℝ), ∀ᵐ point ∂measure,
      (∫ location, values location ∂kernel point) = semigroup (ContinuousMap.toLp 2 measure ℝ values) point)
    (sequence : ℕ → C(X, ℝ)) (forcing : Lp ℝ 2 measure) (bound : ℝ)
    (bounded : ∀ index location, ‖sequence index location‖ ≤ bound)
    (approximationLimit : Tendsto (fun index => ContinuousMap.toLp 2 measure ℝ (sequence index))
      atTop (nhds forcing)) :
    ∀ᵐ point ∂measure, (∫ location, forcing location ∂kernel point) = semigroup forcing point := by
  obtain ⟨inputSelection, inputSelectionStrict, selectedInputLimit⟩ :=
    (tendstoInMeasure_of_tendsto_Lp approximationLimit).exists_seq_tendsto_ae
  have selectedOutputLimit := (semigroup.continuous.tendsto forcing).comp
    (approximationLimit.comp inputSelectionStrict.tendsto_atTop)
  obtain ⟨outputSelection, outputSelectionStrict, selectedOutputAE⟩ :=
    (tendstoInMeasure_of_tendsto_Lp selectedOutputLimit).exists_seq_tendsto_ae
  have continuousRepresentatives : ∀ᵐ location ∂measure, ∀ index : ℕ,
      (ContinuousMap.toLp 2 measure ℝ (sequence index)) location = sequence index location :=
    ae_all_iff.mpr (fun index => ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) measure (sequence index))
  have continuousInputLimit : ∀ᵐ location ∂measure,
      Tendsto (fun index => sequence (inputSelection (outputSelection index)) location)
        atTop (nhds (forcing location)) := by
    filter_upwards [selectedInputLimit, continuousRepresentatives] with location pointLimit representatives
    simpa only [representatives] using pointLimit.comp outputSelectionStrict.tendsto_atTop
  exact ae_kernel_integral_of_bounded_test_limits measure (continuousOperator measure semigroup)
    kernel invariant representation (fun index => sequence (inputSelection (outputSelection index)))
    forcing (semigroup forcing) bound
    (fun index location => bounded (inputSelection (outputSelection index)) location)
    continuousInputLimit selectedOutputAE

end IGS.Sec31.CountableMarkov

#print axioms IGS.Sec31.CountableMarkov.ae_kernel_integral_of_bounded_test_limits
#print axioms IGS.Sec31.CountableMarkov.ae_kernel_integral_of_bounded_continuous_L2_approximation
