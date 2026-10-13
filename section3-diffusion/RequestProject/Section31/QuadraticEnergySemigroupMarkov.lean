import RequestProject.Section31.QuadraticEnergySmallStepContraction
import RequestProject.Section31.QuadraticEnergySemigroup
import RequestProject.Section31.BoundedYosidaInvariantConvex
import RequestProject.Section31.LpClosedMarkovSets

/-! Markov preservation for the genuine strong limit of the actual closed-form
Yosida exponentials. Resolvent preservation comes from the proved minimum. -/
namespace IGS.Sec31.QuadraticEnergySpace
open MeasureTheory Filter Topology
open scoped NNReal
variable {X : Type*} [MeasurableSpace X] (measure : Measure X)
variable (domain : Submodule ℝ (Lp ℝ 2 measure)) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set (Lp ℝ 2 measure)))
    (normalContractions : ∀ (contraction : ℝ → ℝ)
      (lipschitz : LipschitzWith 1 contraction) (zero : contraction 0 = 0)
      (target : closedDomain domain form nonnegative),
      ∃ membership : lipschitz.compLp zero target.val ∈ closedDomain domain form nonnegative,
        closedForm domain form nonnegative closable ⟨lipschitz.compLp zero target.val, membership⟩ ≤
          closedForm domain form nonnegative closable target)

include normalContractions

theorem lp_yosidaSemigroup_preserves_nonnegative
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (forcing : Lp ℝ 2 measure)
    (forcingNonnegative : ∀ᵐ point ∂measure, 0 ≤ forcing point) :
    ∀ᵐ point ∂measure,
      0 ≤ yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time forcing point := by
  exact BoundedYosida.semigroup_mem_of_closed_convex _ (LpMarkov.nonnegativeSet measure)
    (LpMarkov.nonnegativeSet_closed measure) (LpMarkov.nonnegativeSet_convex measure)
    (LpMarkov.zero_mem_nonnegativeSet measure)
    (fun values membership => lp_smallStep_resolvent_preserves_nonnegative measure domain form nonnegative
      closable domainDense step stepPositive stepAtMostOne normalContractions values membership)
    step stepPositive time timeNonnegative forcing forcingNonnegative

theorem lp_yosidaSemigroup_preserves_unit_interval
    (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (forcing : Lp ℝ 2 measure)
    (forcingBounds : ∀ᵐ point ∂measure, 0 ≤ forcing point ∧ forcing point ≤ 1) :
    ∀ᵐ point ∂measure,
      0 ≤ yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time forcing point ∧
      yosidaSemigroup domain form nonnegative closable domainDense step stepPositive stepAtMostOne time forcing point ≤ 1 := by
  exact BoundedYosida.semigroup_mem_of_closed_convex _ (LpMarkov.unitIntervalSet measure)
    (LpMarkov.unitIntervalSet_closed measure) (LpMarkov.unitIntervalSet_convex measure)
    (LpMarkov.zero_mem_unitIntervalSet measure)
    (fun values membership => lp_smallStep_resolvent_preserves_unit_interval measure domain form nonnegative
      closable domainDense step stepPositive stepAtMostOne normalContractions values membership)
    step stepPositive time timeNonnegative forcing forcingBounds

theorem lp_closedSemigroup_preserves_nonnegative (time : ℝ≥0) (forcing : Lp ℝ 2 measure)
    (forcingNonnegative : ∀ᵐ point ∂measure, 0 ≤ forcing point) :
    ∀ᵐ point ∂measure,
      0 ≤ closedSemigroup domain form nonnegative closable domainDense time forcing point := by
  apply (LpMarkov.nonnegativeSet_closed measure).mem_of_tendsto
    (closedSemigroup_approximation_limit domain form nonnegative closable domainDense time forcing)
  apply Filter.Eventually.of_forall
  intro index
  exact lp_yosidaSemigroup_preserves_nonnegative measure domain form nonnegative closable domainDense
    normalContractions (canonicalYosidaStep index) (canonicalYosidaStep_positive index)
    (canonicalYosidaStep_le_one index) time time.coe_nonneg forcing forcingNonnegative

theorem lp_closedSemigroup_preserves_unit_interval (time : ℝ≥0) (forcing : Lp ℝ 2 measure)
    (forcingBounds : ∀ᵐ point ∂measure, 0 ≤ forcing point ∧ forcing point ≤ 1) :
    ∀ᵐ point ∂measure,
      0 ≤ closedSemigroup domain form nonnegative closable domainDense time forcing point ∧
      closedSemigroup domain form nonnegative closable domainDense time forcing point ≤ 1 := by
  apply (LpMarkov.unitIntervalSet_closed measure).mem_of_tendsto
    (closedSemigroup_approximation_limit domain form nonnegative closable domainDense time forcing)
  apply Filter.Eventually.of_forall
  intro index
  exact lp_yosidaSemigroup_preserves_unit_interval measure domain form nonnegative closable domainDense
    normalContractions (canonicalYosidaStep index) (canonicalYosidaStep_positive index)
    (canonicalYosidaStep_le_one index) time time.coe_nonneg forcing forcingBounds

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.lp_yosidaSemigroup_preserves_nonnegative
#print axioms IGS.Sec31.QuadraticEnergySpace.lp_yosidaSemigroup_preserves_unit_interval
#print axioms IGS.Sec31.QuadraticEnergySpace.lp_closedSemigroup_preserves_nonnegative
#print axioms IGS.Sec31.QuadraticEnergySpace.lp_closedSemigroup_preserves_unit_interval
