import RequestProject.Section31.EIGSClosedFormYosidaSemigroup
import RequestProject.Section31.EIGSL2EnergyConstants
import RequestProject.Section31.QuadraticEnergySemigroupKernel

/-! Actual native constants are fixed by the constructed closed-form
semigroup. Density is the existing original-core witness; the energy and
closability facts are supplied by proved EIGS results. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31
open scoped NNReal

set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiClosedSemigroup_constant_of_dense_core (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily connected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (originalDense : Dense (xiContinuousEnergyLpDomain system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive :
        Set (Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass)))) (constant : ℝ) (time : ℝ≥0) :
    let originalDomain := xiContinuousEnergyLpDomain system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system connected loopless unique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
        (xiContinuousLpEnergyConstant system connected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
          resistanceRate ratePositive resistanceVector vectorPositive constant :
          Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass)) =
      (xiContinuousLpEnergyConstant system connected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
          resistanceRate ratePositive resistanceVector vectorPositive constant :
          Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass)) := by
  dsimp only
  exact QuadraticEnergySpace.closedSemigroup_fixed_of_original_energy_zero _ _ _ _ originalDense
    (xiContinuousLpEnergyConstant system connected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive constant)
    (xiContinuousLpEnergyConstant_energy system connected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair constant) time

end EIGS

#print axioms EIGS.xiClosedSemigroup_constant_of_dense_core
