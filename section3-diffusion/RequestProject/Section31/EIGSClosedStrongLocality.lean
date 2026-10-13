import RequestProject.Section31.EIGSClosedContinuousDomain
import RequestProject.Section31.EIGSContinuousCoreLocality

/-! Strong locality on the continuous part of the actual closed domain. Its
continuous elements are first proved to belong to the original finite-energy
domain; arbitrary closed elements are not declared continuous. Compactness of
the space supplies compact support, and the constant neighborhood is open. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31

set_option maxHeartbeats 3000000
variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)

include rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance

theorem xiClosedLpEnergy_associated_eq_zero_of_continuous :
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    ∀ first second : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
    ∀ firstMember : xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair mass first ∈ QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
    ∀ secondMember : xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair mass second ∈ QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
    ∀ neighborhood : Set (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair),
    IsOpen neighborhood → tsupport second ⊆ neighborhood →
    ∀ constant : ℝ, (∀ point ∈ neighborhood, first point = constant) →
      (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable).associated
        ⟨xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair mass first, firstMember⟩
        ⟨xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair mass second, secondMember⟩ = 0 := by
  classical
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  dsimp only
  intro first second firstMember secondMember neighborhood neighborhoodOpen supportSubset constant constantOn
  have firstFinite := (xiContinuous_mem_closedDomain_iff system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair first).1 firstMember
  have secondFinite := (xiContinuous_mem_closedDomain_iff system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair second).1 secondMember
  let firstNative := xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
    metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive ⟨first, firstFinite⟩
  let secondNative := xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
    metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive ⟨second, secondFinite⟩
  have extension := QuadraticEnergySpace.closedForm_associated_extends originalDomain originalForm nonnegative closable
    firstNative secondNative
  have coreZero := xiContinuousLpEnergy_associated_eq_zero_on_core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive mass renormalizationEigenpair
    ⟨first, firstFinite⟩ ⟨second, secondFinite⟩ neighborhood neighborhoodOpen supportSubset constant constantOn
  exact extension.trans coreZero

end EIGS

#print axioms EIGS.xiClosedLpEnergy_associated_eq_zero_of_continuous

