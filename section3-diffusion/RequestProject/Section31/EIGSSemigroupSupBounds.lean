import RequestProject.Section31.EIGSConservativeMarkovSemigroup

/-! Almost-everywhere constant bounds and sup-norm estimates for the actual
native conservative Markov semigroup. No continuous output version is assumed. -/

namespace IGS.Sec31.LpMarkovBounds
open MeasureTheory
variable {X : Type*} [MeasurableSpace X] (measure : Measure X)

theorem preserves_constant_bounds (operator : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (constant : ℝ → Lp ℝ 2 measure)
    (constantAE : ∀ value, (constant value : X → ℝ) =ᵐ[measure] fun _ => value)
    (positive : ∀ forcing : Lp ℝ 2 measure,
      (∀ᵐ point ∂measure, 0 ≤ forcing point) → ∀ᵐ point ∂measure, 0 ≤ operator forcing point)
    (constantFixed : ∀ value, operator (constant value) = constant value)
    (forcing : Lp ℝ 2 measure) (lower upper : ℝ)
    (bounds : ∀ᵐ point ∂measure, lower ≤ forcing point ∧ forcing point ≤ upper) :
    ∀ᵐ point ∂measure, lower ≤ operator forcing point ∧ operator forcing point ≤ upper := by
  have lowerPositive : ∀ᵐ point ∂measure, 0 ≤ (forcing - constant lower) point := by
    filter_upwards [Lp.coeFn_sub forcing (constant lower), constantAE lower, bounds]
      with point subtraction evaluation bound
    simp only [Pi.sub_apply] at subtraction
    rw [subtraction, evaluation]
    exact sub_nonneg.mpr bound.1
  have upperPositive : ∀ᵐ point ∂measure, 0 ≤ (constant upper - forcing) point := by
    filter_upwards [Lp.coeFn_sub (constant upper) forcing, constantAE upper, bounds]
      with point subtraction evaluation bound
    simp only [Pi.sub_apply] at subtraction
    rw [subtraction, evaluation]
    exact sub_nonneg.mpr bound.2
  have lowerOutput := positive (forcing - constant lower) lowerPositive
  have upperOutput := positive (constant upper - forcing) upperPositive
  rw [map_sub, constantFixed] at lowerOutput upperOutput
  filter_upwards [lowerOutput, upperOutput,
    Lp.coeFn_sub (operator forcing) (constant lower),
    Lp.coeFn_sub (constant upper) (operator forcing), constantAE lower, constantAE upper]
    with point lowerBound upperBound lowerSub upperSub lowerEvaluation upperEvaluation
  simp only [Pi.sub_apply] at lowerSub upperSub
  rw [lowerSub, lowerEvaluation] at lowerBound
  rw [upperSub, upperEvaluation] at upperBound
  exact ⟨sub_nonneg.mp lowerBound, sub_nonneg.mp upperBound⟩

section Continuous
variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure measure]

theorem continuous_input_sup_bound
    (operator : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (preservesBounds : ∀ forcing : Lp ℝ 2 measure, ∀ lower upper : ℝ,
      (∀ᵐ point ∂measure, lower ≤ forcing point ∧ forcing point ≤ upper) →
      ∀ᵐ point ∂measure, lower ≤ operator forcing point ∧ operator forcing point ≤ upper)
    (values : C(X, ℝ)) :
    ∀ᵐ point ∂measure, |operator (ContinuousMap.toLp 2 measure ℝ values) point| ≤ ‖values‖ := by
  have inputBounds : ∀ᵐ point ∂measure,
      -‖values‖ ≤ ContinuousMap.toLp 2 measure ℝ values point ∧
        ContinuousMap.toLp 2 measure ℝ values point ≤ ‖values‖ := by
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) measure values] with point evaluation
    rw [evaluation]
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using values.norm_coe_le_norm point)
  filter_upwards [preservesBounds _ _ _ inputBounds] with point bound
  exact abs_le.mpr bound

theorem continuous_input_difference_sup_bound
    (operator : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (preservesBounds : ∀ forcing : Lp ℝ 2 measure, ∀ lower upper : ℝ,
      (∀ᵐ point ∂measure, lower ≤ forcing point ∧ forcing point ≤ upper) →
      ∀ᵐ point ∂measure, lower ≤ operator forcing point ∧ operator forcing point ≤ upper)
    (first second : C(X, ℝ)) :
    ∀ᵐ point ∂measure,
      |operator (ContinuousMap.toLp 2 measure ℝ first) point -
        operator (ContinuousMap.toLp 2 measure ℝ second) point| ≤ ‖first - second‖ := by
  have differenceBound := continuous_input_sup_bound measure operator preservesBounds (first - second)
  rw [map_sub, map_sub] at differenceBound
  filter_upwards [differenceBound,
    Lp.coeFn_sub (operator (ContinuousMap.toLp 2 measure ℝ first))
      (operator (ContinuousMap.toLp 2 measure ℝ second))] with point bound evaluation
  simpa only [evaluation, Pi.sub_apply] using bound

end Continuous
end IGS.Sec31.LpMarkovBounds

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped BoundedContinuousFunction NNReal
set_option maxHeartbeats 3000000
variable {K : ℕ}

def XiSemigroupSupBoundsProperties (system : EIGSData K)
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
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) : Prop :=
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
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
    ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass))),
      let semigroup := QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense
      (∀ (time : ℝ≥0) (forcing : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass)) (lower upper : ℝ),
        (∀ᵐ point ∂(xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass), lower ≤ forcing point ∧ forcing point ≤ upper) →
        ∀ᵐ point ∂(xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass), lower ≤ semigroup time forcing point ∧ semigroup time forcing point ≤ upper) ∧
      (∀ (time : ℝ≥0) (values : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
        ∀ᵐ point ∂(xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass),
          |semigroup time (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass values) point| ≤ ‖values‖) ∧
      (∀ (time : ℝ≥0) (first second : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
        ∀ᵐ point ∂(xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass),
          |semigroup time (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass first) point -
            semigroup time (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass second) point| ≤ ‖first - second‖)


theorem xiSemigroupSupBoundsProperties_of_dense_core (system : EIGSData K)
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
    (originalDense : Dense (xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass)))) :
    XiSemigroupSupBoundsProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance
      lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
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
  have properties := xiConservativeMarkovSemigroupProperties_of_dense_core system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair originalDense
  dsimp only [XiConservativeMarkovSemigroupProperties] at properties
  obtain ⟨density, markov, constantFixed, operatorNorm, zeroTime, addition, jointContinuous⟩ := properties
  let semigroup := QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable density
  let constant := fun value =>
    (xiContinuousLpEnergyConstant system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive value :
      Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass))
  have constantAE := xiContinuousLpEnergyConstant_ae system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  have boundsPreserved := fun time : ℝ≥0 => IGS.Sec31.LpMarkovBounds.preserves_constant_bounds
    (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass)
    (semigroup time) constant constantAE
    (fun forcing positive => (markov time forcing).1 positive) (fun value => constantFixed value time)
  dsimp only [XiSemigroupSupBoundsProperties]
  refine ⟨density, ?_, ?_, ?_⟩
  · exact boundsPreserved
  · intro time values
    exact IGS.Sec31.LpMarkovBounds.continuous_input_sup_bound _ (semigroup time) (boundsPreserved time) values
  · intro time first second
    exact IGS.Sec31.LpMarkovBounds.continuous_input_difference_sup_bound _ (semigroup time) (boundsPreserved time) first second


theorem exists_xiSemigroupSupBounds_of_rules (system : EIGSData K)
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
      XiSemigroupSupBoundsProperties system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
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
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair, ?_⟩
  exact xiSemigroupSupBoundsProperties_of_dense_core system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair originalDense

end EIGS

#print axioms IGS.Sec31.LpMarkovBounds.preserves_constant_bounds
#print axioms IGS.Sec31.LpMarkovBounds.continuous_input_sup_bound
#print axioms IGS.Sec31.LpMarkovBounds.continuous_input_difference_sup_bound
#print axioms EIGS.xiSemigroupSupBoundsProperties_of_dense_core
#print axioms EIGS.exists_xiSemigroupSupBounds_of_rules
