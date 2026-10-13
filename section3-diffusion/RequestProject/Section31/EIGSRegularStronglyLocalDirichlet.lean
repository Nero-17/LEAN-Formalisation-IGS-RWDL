import RequestProject.Section31.EIGSClosedLpEnergyWithoutPrimitive
import RequestProject.Section31.EIGSClosedMarkov
import RequestProject.Section31.EIGSClosedRegularity
import RequestProject.Section31.EIGSClosedStrongLocality

/-! An original-rule construction of the actual regular strongly local
Dirichlet form. All conclusions refer to one explicitly constructed native L2
closed domain and quadratic form. Strong locality is stated on D intersect C_c;
the actual compact space makes C_c equal to C. No process or quasi-continuous
representative is asserted. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31

set_option maxHeartbeats 3000000

variable {K : ℕ}

def XiRegularStronglyLocalDirichletProperties (system : EIGSData K)
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
      (system.ruleFamily connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) : Prop :=
    letI := xiCompletion_compactSpace system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let originalDomain := xiContinuousEnergyLpDomain system connected lengths lengthsPositive
        distanceRate distanceRateGreaterThanOne metricEigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive
      let originalForm := xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive
        distanceRate distanceRateGreaterThanOne metricEigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system connected lengths lengthsPositive
        distanceRate distanceRateGreaterThanOne metricEigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
        intro sequence energyCauchy ambientZero
        exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system connected loopless unique plantingNonadjacent
          distancePositive oneColourDistance lengths lengthsPositive
          distanceRate distanceRateGreaterThanOne metricEigenpair mass
          resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
          (by simpa using ambientZero.norm)
      (∀ values, 0 ≤ (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable) values) ∧
      CompleteSpace (QuadraticEnergySpace (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative) (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable) (QuadraticEnergySpace.closedForm_nonnegative originalDomain originalForm nonnegative closable)) ∧
      Dense ((QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative) : Set (Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive
        distanceRate distanceRateGreaterThanOne metricEigenpair mass))) ∧
      (∀ values : originalDomain, ∃ membership : values.val ∈ (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative),
        (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable) ⟨values.val, membership⟩ = originalForm values) ∧
      (∀ values : QuadraticEnergySpace (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative) (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable) (QuadraticEnergySpace.closedForm_nonnegative originalDomain originalForm nonnegative closable),
        ‖values‖ ^ 2 = (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable) values.value + ‖values.value.val‖ ^ 2) ∧
      (∀ (contraction : ℝ → ℝ) (contractionLipschitz : LipschitzWith 1 contraction)
          (contractionZero : contraction 0 = 0) (target : (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative)),
        ∃ membership : contractionLipschitz.compLp contractionZero target.val ∈ (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative),
          (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable) ⟨contractionLipschitz.compLp contractionZero target.val, membership⟩ ≤ (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable) target) ∧
      (∀ (target : C(XiMetricCompletion system connected lengths lengthsPositive
          distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
          (tolerance : ℝ), 0 < tolerance →
        ∃ approximation : xiContinuousFiniteEnergyDomain system connected lengths lengthsPositive
            distanceRate distanceRateGreaterThanOne metricEigenpair
            resistanceRate ratePositive resistanceVector vectorPositive,
          ∀ point, |approximation.val point - target point| < tolerance) ∧
      (∀ target : (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative), ∃ sequence : ℕ → originalDomain,
        Tendsto (fun index => (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable)
          (⟨(sequence index).val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative (sequence index)⟩ - target) +
            ‖(sequence index).val - target.val‖ ^ 2) atTop (nhds 0)) ∧
      (∀ target : C(XiMetricCompletion system connected lengths lengthsPositive
          distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
        xiContinuousL2Map system connected lengths lengthsPositive
          distanceRate distanceRateGreaterThanOne metricEigenpair mass target ∈ (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative) ↔
        target ∈ xiContinuousFiniteEnergyDomain system connected lengths lengthsPositive
          distanceRate distanceRateGreaterThanOne metricEigenpair
          resistanceRate ratePositive resistanceVector vectorPositive) ∧
      (∀ first second : C(XiMetricCompletion system connected lengths lengthsPositive
          distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
        ∀ firstMember : xiContinuousL2Map system connected lengths lengthsPositive
          distanceRate distanceRateGreaterThanOne metricEigenpair mass first ∈ (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative),
        ∀ secondMember : xiContinuousL2Map system connected lengths lengthsPositive
          distanceRate distanceRateGreaterThanOne metricEigenpair mass second ∈ (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative),
        ∀ neighborhood : Set (XiMetricCompletion system connected lengths lengthsPositive
          distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair),
        IsOpen neighborhood → tsupport second ⊆ neighborhood →
        ∀ constant : ℝ, (∀ point ∈ neighborhood, first point = constant) →
          (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable).associated
            ⟨xiContinuousL2Map system connected lengths lengthsPositive
              distanceRate distanceRateGreaterThanOne metricEigenpair mass first, firstMember⟩
            ⟨xiContinuousL2Map system connected lengths lengthsPositive
              distanceRate distanceRateGreaterThanOne metricEigenpair mass second, secondMember⟩ = 0)

theorem xiRegularStronglyLocalDirichletProperties_of_dense_core (system : EIGSData K)
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
          distanceRateGreaterThanOne metricEigenpair mass)))) :
    XiRegularStronglyLocalDirichletProperties system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
      lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  classical
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let originalDomain := xiContinuousEnergyLpDomain system connected lengths lengthsPositive
    distanceRate distanceRateGreaterThanOne metricEigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive
    distanceRate distanceRateGreaterThanOne metricEigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system connected lengths lengthsPositive
    distanceRate distanceRateGreaterThanOne metricEigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system connected loopless unique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  have regular := xiClosedLpEnergy_regular_core system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
    mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  dsimp only [XiRegularStronglyLocalDirichletProperties]
  refine ⟨
    QuadraticEnergySpace.closedForm_nonnegative originalDomain originalForm nonnegative closable,
    QuadraticEnergySpace.closedEnergySpace_complete originalDomain originalForm nonnegative closable,
    QuadraticEnergySpace.closedDomain_dense originalDomain originalForm nonnegative originalDense,
    ?_, ?_, ?_, regular.1, regular.2, ?_, ?_⟩
  · intro values
    exact ⟨QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative values,
      QuadraticEnergySpace.closedForm_extends originalDomain originalForm nonnegative closable values⟩
  · exact QuadraticEnergySpace.norm_sq _ _ _
  · intro contraction contractionLipschitz contractionZero target
    exact xiClosedLpEnergy_normal_contraction system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
      lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      contraction contractionLipschitz contractionZero target
  · exact xiContinuous_mem_closedDomain_iff system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
      lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  · exact xiClosedLpEnergy_associated_eq_zero_of_continuous system connected loopless unique plantingNonadjacent distancePositive
      oneColourDistance lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair


theorem exists_xiRegularStronglyLocalDirichletForm_of_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
    letI := xiCompletion_compactSpace system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (connected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      XiRegularStronglyLocalDirichletProperties system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
        parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  classical
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system connected distancePositive
  letI := xiCompletion_compactSpace system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (connected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
      originalDense, originalNonnegative⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system connected loopless unique plantingNonadjacent distancePositive
  exact ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
    xiRegularStronglyLocalDirichletProperties_of_dense_core system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair originalDense⟩

end EIGS

#print axioms EIGS.xiRegularStronglyLocalDirichletProperties_of_dense_core
#print axioms EIGS.exists_xiRegularStronglyLocalDirichletForm_of_rules
