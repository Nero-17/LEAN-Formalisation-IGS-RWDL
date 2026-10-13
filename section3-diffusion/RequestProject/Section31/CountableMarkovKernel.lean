import RequestProject.Section31.CountableMarkovPointMeasure
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Probability.Kernel.Defs

/-! A genuine fixed-time measurable probability kernel, constructed from the
actual point functionals and default Dirac measures. No Chapman--Kolmogorov or
all-starting-point process statement is assumed or asserted. -/

namespace IGS.Sec31.CountableMarkov
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal BoundedContinuousFunction

set_option maxHeartbeats 2000000

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    (measure : Measure X) [IsFiniteMeasure measure]
    (operator : C(X, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (tests : Submodule ℚ C(X, ℝ))
    (dense : Dense (tests : Set C(X, ℝ))) (oneMem : (1 : C(X, ℝ)) ∈ tests)

noncomputable def extendedPointMeasure (defaultPoint point : X) : Measure X := by
  classical
  exact if good : GoodPoint measure operator tests point then
    pointMeasure measure operator tests dense oneMem point good
  else Measure.dirac defaultPoint

instance extendedPointMeasure_isProbability (defaultPoint point : X) :
    IsProbabilityMeasure (extendedPointMeasure measure operator tests dense oneMem defaultPoint point) := by
  classical
  by_cases good : GoodPoint measure operator tests point
  · simpa only [extendedPointMeasure, dif_pos good] using
      pointMeasure_isProbability measure operator tests dense oneMem point good
  · simp only [extendedPointMeasure, dif_neg good]
    infer_instance

theorem extendedPointMeasure_integral (defaultPoint point : X) (values : C(X, ℝ)) :
    ∫ location, values location
        ∂(extendedPointMeasure measure operator tests dense oneMem defaultPoint point) =
      extendedPointFunctional measure operator tests defaultPoint point values := by
  classical
  by_cases good : GoodPoint measure operator tests point
  · simpa only [extendedPointMeasure, dif_pos good, extendedPointFunctional, dif_pos good] using
      pointMeasure_integral measure operator tests dense oneMem point good values
  · simp only [extendedPointMeasure, extendedPointFunctional, dif_neg good,
      ContinuousMap.evalCLM_apply]
    exact integral_dirac values defaultPoint

theorem extendedPointMeasure_apply_closed_measurable [Countable tests]
    (defaultPoint : X) (closedSet : Set X) (closed : IsClosed closedSet) :
    Measurable (fun point =>
      extendedPointMeasure measure operator tests dense oneMem defaultPoint point closedSet) := by
  have approximationMeasurable : ∀ index : ℕ, Measurable (fun point =>
      ∫⁻ location, closed.apprSeq index location
        ∂(extendedPointMeasure measure operator tests dense oneMem defaultPoint point)) := by
    intro index
    let values : C(X, ℝ) :=
      ⟨fun location => (closed.apprSeq index location : ℝ),
        NNReal.continuous_coe.comp (closed.apprSeq index).continuous⟩
    have equality :
        (fun point => ∫⁻ location, closed.apprSeq index location
          ∂(extendedPointMeasure measure operator tests dense oneMem defaultPoint point)) =
        (fun point => ENNReal.ofReal
          (extendedPointFunctional measure operator tests defaultPoint point values)) := by
      funext point
      rw [lintegral_coe_eq_integral _
        (BoundedContinuousFunction.integrable_of_nnreal
          (extendedPointMeasure measure operator tests dense oneMem defaultPoint point)
          (closed.apprSeq index))]
      congr 1
      exact extendedPointMeasure_integral measure operator tests dense oneMem defaultPoint point values
    rw [equality]
    exact (extendedPointFunctional_measurable measure operator tests dense defaultPoint values).ennreal_ofReal
  apply measurable_of_tendsto_metrizable approximationMeasurable
  apply tendsto_pi_nhds.mpr
  intro point
  exact HasOuterApproxClosed.tendsto_lintegral_apprSeq closed
    (extendedPointMeasure measure operator tests dense oneMem defaultPoint point)

theorem extendedPointMeasure_measurable [Countable tests] (defaultPoint : X) :
    Measurable (extendedPointMeasure measure operator tests dense oneMem defaultPoint) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (μ := extendedPointMeasure measure operator tests dense oneMem defaultPoint)
    (S := {closedSet : Set X | IsClosed closedSet})
  · rw [BorelSpace.measurable_eq (α := X), borel_eq_generateFrom_isClosed]
  · exact isPiSystem_isClosed
  · intro closedSet closed
    exact extendedPointMeasure_apply_closed_measurable measure operator tests dense oneMem
      defaultPoint closedSet closed

/-- The kernel is bundled only after proving its actual measure-valued map is
measurable. -/
noncomputable def fixedTimeKernel [Countable tests] (defaultPoint : X) : Kernel X X :=
  ⟨extendedPointMeasure measure operator tests dense oneMem defaultPoint,
    extendedPointMeasure_measurable measure operator tests dense oneMem defaultPoint⟩

instance fixedTimeKernel_isMarkov [Countable tests] (defaultPoint : X) :
    IsMarkovKernel (fixedTimeKernel measure operator tests dense oneMem defaultPoint) := by
  constructor
  intro point
  change IsProbabilityMeasure
    (extendedPointMeasure measure operator tests dense oneMem defaultPoint point)
  infer_instance

theorem fixedTimeKernel_integral [Countable tests] (defaultPoint point : X) (values : C(X, ℝ)) :
    ∫ location, values location
        ∂(fixedTimeKernel measure operator tests dense oneMem defaultPoint point) =
      extendedPointFunctional measure operator tests defaultPoint point values :=
  extendedPointMeasure_integral measure operator tests dense oneMem defaultPoint point values

theorem ae_fixedTimeKernel_integral [Countable tests]
    (supBound : ∀ values : C(X, ℝ),
      ∀ᵐ point ∂measure, |operator values point| ≤ ‖values‖)
    (goodAE : ∀ᵐ point ∂measure, GoodPoint measure operator tests point)
    (defaultPoint : X) (values : C(X, ℝ)) :
    ∀ᵐ point ∂measure,
      ∫ location, values location
          ∂(fixedTimeKernel measure operator tests dense oneMem defaultPoint point) =
        operator values point := by
  filter_upwards [extendedPointFunctional_ae_eq measure operator tests dense supBound goodAE defaultPoint values]
    with point agreement
  rw [fixedTimeKernel_integral measure operator tests dense oneMem defaultPoint point]
  exact agreement

theorem ae_fixedTimeKernel_integral_of_semigroup [Countable tests]
    (semigroup : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (preservesBounds : ∀ forcing : Lp ℝ 2 measure, ∀ lower upper : ℝ,
      (∀ᵐ point ∂measure, lower ≤ forcing point ∧ forcing point ≤ upper) →
      ∀ᵐ point ∂measure, lower ≤ semigroup forcing point ∧ semigroup forcing point ≤ upper)
    (positive : ∀ forcing : Lp ℝ 2 measure,
      (∀ᵐ point ∂measure, 0 ≤ forcing point) → ∀ᵐ point ∂measure, 0 ≤ semigroup forcing point)
    (oneFixed : semigroup (ContinuousMap.toLp 2 measure ℝ (1 : C(X, ℝ))) =
      ContinuousMap.toLp 2 measure ℝ (1 : C(X, ℝ)))
    (defaultPoint : X) (values : C(X, ℝ)) :
    ∀ᵐ point ∂measure,
      ∫ location, values location
          ∂(fixedTimeKernel measure (continuousOperator measure semigroup) tests dense oneMem defaultPoint point) =
        semigroup (ContinuousMap.toLp 2 measure ℝ values) point := by
  exact ae_fixedTimeKernel_integral measure (continuousOperator measure semigroup) tests dense oneMem
    (LpMarkovBounds.continuous_input_sup_bound measure semigroup preservesBounds)
    (ae_goodPoint_of_semigroup measure tests semigroup preservesBounds positive oneFixed) defaultPoint values

end IGS.Sec31.CountableMarkov

#print axioms IGS.Sec31.CountableMarkov.extendedPointMeasure_isProbability
#print axioms IGS.Sec31.CountableMarkov.extendedPointMeasure_measurable
#print axioms IGS.Sec31.CountableMarkov.fixedTimeKernel_isMarkov
#print axioms IGS.Sec31.CountableMarkov.ae_fixedTimeKernel_integral
#print axioms IGS.Sec31.CountableMarkov.ae_fixedTimeKernel_integral_of_semigroup
