import RequestProject.Section31.DyadicMarkovTwoTimeLaw
import RequestProject.Section31.KernelPairStochasticContinuity
import Mathlib.Topology.Instances.Rat

/-! Stochastic continuity of the actual stationary dyadic total process.
The actual two-time joint law and genuine C0 kernel-pair limit prove the
displacement probabilities tend to zero. The original-rule consumer fills
all analytic inputs from the same native closed form and rational kernel.
This asserts no continuous sample paths or Hunt property. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Filter Topology
open scoped ProbabilityTheory NNRat NNReal BoundedContinuousFunction
set_option maxHeartbeats 3000000
noncomputable section

instance dyadicTimeMetricSpace : MetricSpace DyadicTime := by
  unfold DyadicTime
  infer_instance

def dyadicTimeGap (firstTime secondTime : DyadicTime) : ℚ≥0 :=
  max (secondTime.val - firstTime.val) (firstTime.val - secondTime.val)

theorem dyadicTimeGap_continuous (fixedTime : DyadicTime) :
    Continuous (fun time : DyadicTime => dyadicTimeGap time fixedTime) :=
  (continuous_const.sub continuous_subtype_val).max
    (continuous_subtype_val.sub continuous_const)

@[simp] theorem dyadicTimeGap_self (time : DyadicTime) : dyadicTimeGap time time = 0 := by
  simp [dyadicTimeGap]

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [StandardBorelSpace X] [Nonempty X]

theorem dyadicPathLaw_displacement_event (family : ℚ≥0 → Kernel X X)
    (markov : ∀ time, IsMarkovKernel (family time)) (initial : Measure X)
    [IsProbabilityMeasure initial] (invariant : ∀ time, (family time).Invariant initial)
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime))
    (firstTime secondTime : DyadicTime) (epsilon : ℝ) :
    (dyadicPathLaw family markov initial)
        {path | epsilon < dist (path firstTime) (path secondTime)} =
      (initial ⊗ₘ family (dyadicTimeGap firstTime secondTime))
        {pair | epsilon < dist pair.1 pair.2} := by
  have measurableEvent : MeasurableSet {pair : X × X | epsilon < dist pair.1 pair.2} :=
    (isOpen_lt continuous_const (continuous_fst.dist continuous_snd)).measurableSet
  by_cases ordered : firstTime.val ≤ secondTime.val
  · have gap : dyadicTimeGap firstTime secondTime = secondTime.val - firstTime.val := by
      simp only [dyadicTimeGap, tsub_eq_zero_of_le ordered]
      exact max_eq_left (zero_le _)
    have mappedEvent : ((dyadicPathLaw family markov initial).map
        (fun path => (path firstTime, path secondTime)))
          {pair | epsilon < dist pair.1 pair.2} =
        (dyadicPathLaw family markov initial)
          {path | epsilon < dist (path firstTime) (path secondTime)} := by
      rw [Measure.map_apply (f := fun path : DyadicTime → X => (path firstTime, path secondTime))
        ((measurable_pi_apply _).prodMk (measurable_pi_apply _)) measurableEvent]
      rfl
    rw [gap, ← mappedEvent,
      dyadicPathLaw_ordered_pair family markov initial invariant zeroLaw addLaw firstTime secondTime ordered]
  · have reverseOrdered : secondTime.val ≤ firstTime.val := le_of_lt (lt_of_not_ge ordered)
    have gap : dyadicTimeGap firstTime secondTime = firstTime.val - secondTime.val := by
      simp only [dyadicTimeGap, tsub_eq_zero_of_le reverseOrdered]
      exact max_eq_right (zero_le _)
    have mappedEvent : ((dyadicPathLaw family markov initial).map
        (fun path => (path secondTime, path firstTime)))
          {pair | epsilon < dist pair.1 pair.2} =
        (dyadicPathLaw family markov initial)
          {path | epsilon < dist (path firstTime) (path secondTime)} := by
      rw [Measure.map_apply (f := fun path : DyadicTime → X => (path secondTime, path firstTime))
        ((measurable_pi_apply _).prodMk (measurable_pi_apply _)) measurableEvent]
      congr 1
      ext path
      change (epsilon < dist (path secondTime) (path firstTime)) ↔
        epsilon < dist (path firstTime) (path secondTime)
      rw [dist_comm (path secondTime) (path firstTime)]
    rw [gap, ← mappedEvent,
      dyadicPathLaw_ordered_pair family markov initial invariant zeroLaw addLaw secondTime firstTime reverseOrdered]

def StationaryDyadicStochasticContinuity (initial : Measure X) [IsProbabilityMeasure initial]
    (family : ℚ≥0 → Kernel X X) (markov : ∀ time, IsMarkovKernel (family time)) : Prop :=
  ∀ (fixedTime : DyadicTime) (epsilon : ℝ), 0 < epsilon →
    Tendsto (fun time : DyadicTime => (dyadicPathLaw family markov initial)
      {path | epsilon < dist (path time) (path fixedTime)}) (nhds fixedTime) (nhds 0)

theorem dyadicPathLaw_stochasticallyContinuous (measure : ProbabilityMeasure X)
    (family : ℚ≥0 → Kernel X X) (markov : ∀ time, IsMarkovKernel (family time))
    (invariant : ∀ time, (family time).Invariant (measure : Measure X))
    (zeroLaw : family 0 = Kernel.id)
    (addLaw : ∀ firstTime secondTime,
      family secondTime ∘ₖ family firstTime = family (firstTime + secondTime))
    (operators : ℚ≥0 → Lp ℝ 2 (measure : Measure X) →L[ℝ] Lp ℝ 2 (measure : Measure X))
    (representation : ∀ time (function : X →ᵇ ℝ), ∀ᵐ source ∂(measure : Measure X),
      (∫ target, function target ∂family time source) =
        operators time (BoundedContinuousFunction.toLp 2 (measure : Measure X) ℝ function) source)
    (strongToIdentity : ∀ values : Lp ℝ 2 (measure : Measure X),
      Tendsto (fun time => operators time values) (nhds 0) (nhds values)) :
    StationaryDyadicStochasticContinuity (measure : Measure X) family markov := by
  intro fixedTime epsilon positive
  have kernelConvergence := StationaryPair.kernel_pair_distance_probability_tendsto_zero
    measure family markov operators representation strongToIdentity epsilon positive
  have gapConvergence : Tendsto (fun time : DyadicTime => dyadicTimeGap time fixedTime)
      (nhds fixedTime) (nhds 0) := by
    simpa only [dyadicTimeGap_self] using (dyadicTimeGap_continuous fixedTime).tendsto fixedTime
  have eventIdentity : (fun time : DyadicTime => (dyadicPathLaw family markov (measure : Measure X))
      {path | epsilon < dist (path time) (path fixedTime)}) =
      (fun time : DyadicTime => (StationaryPair.probability measure
        (family (dyadicTimeGap time fixedTime)) (markov _) : Measure (X × X))
          {pair | epsilon < dist pair.1 pair.2}) := by
    funext time
    exact dyadicPathLaw_displacement_event family markov (measure : Measure X) invariant
      zeroLaw addLaw time fixedTime epsilon
  rw [eventIdentity]
  exact kernelConvergence.comp gapConvergence

end
end IGS.Sec31.DiscreteMarkov

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology
open scoped NNRat NNReal
set_option maxHeartbeats 3000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem closedSemigroup_rational_tendsto_identity (domain : Submodule ℝ H)
    (form : QuadraticForm ℝ domain) (nonnegative : ∀ values, 0 ≤ form values)
    (closable : SequentiallyClosable domain form) (domainDense : Dense (domain : Set H))
    (values : H) :
    Tendsto (fun time : ℚ≥0 => closedSemigroup domain form nonnegative closable domainDense
      (time : ℝ≥0) values) (nhds 0) (nhds values) := by
  have realCastContinuous : Continuous (fun time : ℚ≥0 => (time : ℝ)) := by
    simpa only [Rat.cast_nnratCast] using
      Rat.continuous_coe_real.comp (continuous_subtype_val : Continuous (fun time : ℚ≥0 => (time : ℚ)))
  have rationalCastContinuous : Continuous (fun time : ℚ≥0 => (time : ℝ≥0)) := by
    change Continuous (fun time : ℚ≥0 => (⟨(time : ℝ), NNRat.cast_nonneg time⟩ : ℝ≥0))
    exact realCastContinuous.subtype_mk _
  have timeConvergence : Tendsto (fun time : ℚ≥0 => (time : ℝ≥0)) (nhds 0) (nhds 0) := by
    simpa only [NNRat.cast_zero] using rationalCastContinuous.tendsto 0
  have pairConvergence : Tendsto (fun time : ℚ≥0 => (values, (time : ℝ≥0)))
      (nhds 0) (nhds (values, 0)) := tendsto_const_nhds.prodMk_nhds timeConvergence
  have orbitConvergence :=
    (closedSemigroup_joint_continuous domain form nonnegative closable domainDense).tendsto (values, 0)
  simpa only [Function.comp_apply, closedSemigroup_zero, ContinuousLinearMap.id_apply] using
    orbitConvergence.comp pairConvergence

end IGS.Sec31.QuadraticEnergySpace


namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped BoundedContinuousFunction NNReal NNRat ProbabilityTheory
set_option maxHeartbeats 3000000
variable {K : ℕ}

def XiDyadicStochasticContinuityProperties (system : EIGSData K)
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
      ∀ defaultPoint : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair,
      letI : Nonempty (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) := ⟨defaultPoint⟩
      ∃ transition : ℚ≥0 → ProbabilityTheory.Kernel (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair),
        ∃ markov : ∀ time, ProbabilityTheory.IsMarkovKernel (transition time),
        (∀ (time : ℚ≥0) (values : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
          ∀ᵐ point ∂(xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass),
            ∫ location, values location ∂(transition time point) =
              semigroup (time : ℝ≥0) (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
                distanceRateGreaterThanOne metricEigenpair mass values) point) ∧
        (∀ time, (transition time).Invariant
          (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass)) ∧
        transition 0 = ProbabilityTheory.Kernel.id ∧
        (∀ firstTime secondTime : ℚ≥0,
          transition secondTime ∘ₖ transition firstTime = transition (firstTime + secondTime)) ∧
        DiscreteMarkov.RationalSkeletonProperties
          (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass) transition markov ∧
        DiscreteMarkov.DyadicProcessProperties transition markov ∧
        DiscreteMarkov.StationaryDyadicStochasticContinuity
          (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass) transition markov


theorem xiDyadicStochasticContinuityProperties_of_dense_core (system : EIGSData K)
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
    XiDyadicStochasticContinuityProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance
      lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  have kernelProperties := xiRationalMarkovKernelProperties_of_dense_core system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair originalDense
  dsimp only [XiRationalMarkovKernelProperties] at kernelProperties
  obtain ⟨density, kernelForDefault⟩ := kernelProperties
  dsimp only [XiDyadicStochasticContinuityProperties]
  refine ⟨density, ?_⟩
  intro defaultPoint
  obtain ⟨transition, markov, representation, invariant, zeroLaw, addLaw⟩ := kernelForDefault defaultPoint
  letI : Nonempty (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) := ⟨defaultPoint⟩
  refine ⟨transition, markov, representation, invariant, zeroLaw, addLaw, ?_, ?_, ?_⟩
  · exact DiscreteMarkov.rationalSkeletonProperties_of_family
      (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass) transition markov invariant zeroLaw addLaw
  · exact DiscreteMarkov.dyadicProcessProperties_of_family transition markov zeroLaw addLaw
  · let initial : ProbabilityMeasure
        (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :=
      ⟨xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass, inferInstance⟩
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
    let semigroup := QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable density
    refine DiscreteMarkov.dyadicPathLaw_stochasticallyContinuous initial transition markov invariant zeroLaw addLaw
      (fun time => semigroup (time : ℝ≥0)) ?_ ?_
    · intro time function
      simpa only [xiContinuousL2Map, ContinuousMap.toLp_comp_toContinuousMap] using
        representation time function.toContinuousMap
    · intro values
      exact QuadraticEnergySpace.closedSemigroup_rational_tendsto_identity originalDomain originalForm
        nonnegative closable density values



theorem exists_xiDyadicStochasticContinuity_of_rules (system : EIGSData K)
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
      XiDyadicStochasticContinuityProperties system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
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
  exact xiDyadicStochasticContinuityProperties_of_dense_core system connected loopless unique plantingNonadjacent distancePositive oneColourDistance
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceRateGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair originalDense

end EIGS

#print axioms EIGS.xiDyadicStochasticContinuityProperties_of_dense_core
#print axioms EIGS.exists_xiDyadicStochasticContinuity_of_rules



#print axioms IGS.Sec31.DiscreteMarkov.dyadicPathLaw_displacement_event
#print axioms IGS.Sec31.DiscreteMarkov.dyadicPathLaw_stochasticallyContinuous
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_rational_tendsto_identity
