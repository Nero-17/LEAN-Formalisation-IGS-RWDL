import RequestProject.Section31.EIGSStationaryPairMeasure
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! Weak convergence of the genuine stationary pair probabilities. The
product-test density argument is proved here, and the native consumer supplies
the product-test convergence using the actual finite and limit kernels. -/

namespace IGS.Sec31.StationaryPair

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 4000000

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

def productTest (first second : C(Space, ℝ)) : C(Space × Space, ℝ) :=
  first.comp ContinuousMap.fst * second.comp ContinuousMap.snd

def productSpan : Submodule ℝ C(Space × Space, ℝ) :=
  Submodule.span ℝ (Set.range fun tests : C(Space, ℝ) × C(Space, ℝ) =>
    productTest tests.1 tests.2)

omit [CompactSpace Space] in
theorem productTest_mem (first second : C(Space, ℝ)) :
    productTest first second ∈ (productSpan : Submodule ℝ C(Space × Space, ℝ)) :=
  Submodule.subset_span ⟨(first, second), rfl⟩

def productAlgebra : Subalgebra ℝ C(Space × Space, ℝ) where
  carrier := {function | function ∈ (productSpan : Submodule ℝ C(Space × Space, ℝ))}
  zero_mem' := (productSpan).zero_mem
  add_mem' := (productSpan).add_mem
  one_mem' := by
    simpa [productTest] using productTest_mem (1 : C(Space, ℝ)) 1
  algebraMap_mem' scalar := by
    have constant := (productSpan : Submodule ℝ C(Space × Space, ℝ)).smul_mem
      scalar (productTest_mem (1 : C(Space, ℝ)) 1)
    simpa [productTest, Algebra.algebraMap_eq_smul_one] using constant
  mul_mem' := by
    intro first second firstMem secondMem
    change first * second ∈ (productSpan : Submodule ℝ C(Space × Space, ℝ))
    apply Submodule.span_induction₂ (p := fun first second _ _ =>
      first * second ∈ (productSpan : Submodule ℝ C(Space × Space, ℝ)))
      (s := Set.range fun tests : C(Space, ℝ) × C(Space, ℝ) => productTest tests.1 tests.2)
      (t := Set.range fun tests : C(Space, ℝ) × C(Space, ℝ) => productTest tests.1 tests.2)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ firstMem secondMem
    · intro first second firstMem secondMem
      obtain ⟨⟨firstLeft, firstRight⟩, rfl⟩ := firstMem
      obtain ⟨⟨secondLeft, secondRight⟩, rfl⟩ := secondMem
      have identity : productTest firstLeft firstRight * productTest secondLeft secondRight =
          productTest (firstLeft * secondLeft) (firstRight * secondRight) := by
        ext point
        simp only [productTest, ContinuousMap.mul_apply, ContinuousMap.comp_apply,
          ContinuousMap.fst_apply, ContinuousMap.snd_apply]
        ring
      rw [identity]
      exact productTest_mem _ _
    · intro second _
      simp
    · intro first _
      simp
    · intro first second third _ _ _ firstMem secondMem
      simpa only [add_mul] using (productSpan).add_mem firstMem secondMem
    · intro first second third _ _ _ firstMem secondMem
      simpa only [mul_add] using (productSpan).add_mem firstMem secondMem
    · intro scalar first second _ _ firstMem
      simpa only [smul_mul_assoc] using (productSpan).smul_mem scalar firstMem
    · intro scalar first second _ _ firstMem
      simpa only [mul_smul_comm] using (productSpan).smul_mem scalar firstMem

omit [CompactSpace Space] in
theorem productAlgebra_separatesPoints :
    (productAlgebra : Subalgebra ℝ C(Space × Space, ℝ)).SeparatesPoints := by
  intro first second different
  by_cases firstDifferent : first.1 ≠ second.1
  · let distanceTest : C(Space, ℝ) := ⟨fun point => dist point first.1, continuous_id.dist continuous_const⟩
    refine ⟨productTest distanceTest 1, ⟨productTest distanceTest 1,
      productTest_mem _ _, rfl⟩, ?_⟩
    intro equality
    apply firstDifferent
    have zeroDistance : dist second.1 first.1 = 0 := by
      simpa [productTest, distanceTest] using equality.symm
    exact (dist_eq_zero.mp zeroDistance).symm
  · have secondDifferent : first.2 ≠ second.2 := by
      intro equality
      exact different (Prod.ext (not_ne_iff.mp firstDifferent) equality)
    let distanceTest : C(Space, ℝ) := ⟨fun point => dist point first.2, continuous_id.dist continuous_const⟩
    refine ⟨productTest 1 distanceTest, ⟨productTest 1 distanceTest,
      productTest_mem _ _, rfl⟩, ?_⟩
    intro equality
    apply secondDifferent
    have zeroDistance : dist second.2 first.2 = 0 := by
      simpa [productTest, distanceTest] using equality.symm
    exact (dist_eq_zero.mp zeroDistance).symm

theorem exists_productSpan_uniform_approximation (function : C(Space × Space, ℝ))
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ approximation ∈ (productSpan : Submodule ℝ C(Space × Space, ℝ)),
      ‖approximation - function‖ < epsilon := by
  obtain ⟨approximation, close⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      (productAlgebra : Subalgebra ℝ C(Space × Space, ℝ))
      productAlgebra_separatesPoints function epsilon positive
  exact ⟨approximation, approximation.property, close⟩

variable [MeasurableSpace Space] [BorelSpace Space]

theorem continuous_integrable (measure : ProbabilityMeasure (Space × Space))
    (function : C(Space × Space, ℝ)) :
    Integrable function (measure : Measure (Space × Space)) := by
  exact Integrable.of_bound function.continuous.measurable.aestronglyMeasurable
    ‖function‖ (Eventually.of_forall function.norm_coe_le_norm)

theorem integral_difference_le (measure : ProbabilityMeasure (Space × Space))
    (first second : C(Space × Space, ℝ)) :
    ‖(∫ point, first point ∂(measure : Measure _)) -
      (∫ point, second point ∂(measure : Measure _))‖ ≤ ‖first - second‖ := by
  rw [← integral_sub (continuous_integrable measure first) (continuous_integrable measure second)]
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := (measure : Measure (Space × Space)))
      (Eventually.of_forall (first - second).norm_coe_le_norm))

theorem productSpan_integral_tendsto {Index : Type*} {filter : Filter Index}
    (measures : Index → ProbabilityMeasure (Space × Space))
    (limitMeasure : ProbabilityMeasure (Space × Space))
    (productConvergence : ∀ first second : Space →ᵇ ℝ,
      Tendsto (fun index => ∫ pair : Space × Space, first pair.1 * second pair.2
        ∂(measures index : Measure _)) filter
        (nhds (∫ pair : Space × Space, first pair.1 * second pair.2
          ∂(limitMeasure : Measure _))))
    {function : C(Space × Space, ℝ)} (membership : function ∈ productSpan) :
    Tendsto (fun index => ∫ pair, function pair ∂(measures index : Measure _)) filter
      (nhds (∫ pair, function pair ∂(limitMeasure : Measure _))) := by
  induction membership using Submodule.span_induction with
  | mem function membership =>
    obtain ⟨⟨first, second⟩, rfl⟩ := membership
    simpa only [productTest, ContinuousMap.mul_apply, ContinuousMap.comp_apply,
      ContinuousMap.fst_apply, ContinuousMap.snd_apply,
      ContinuousMap.linearIsometryBoundedOfCompact_apply_apply] using
      productConvergence (ContinuousMap.linearIsometryBoundedOfCompact Space ℝ ℝ first)
        (ContinuousMap.linearIsometryBoundedOfCompact Space ℝ ℝ second)
  | zero => simpa using (tendsto_const_nhds : Tendsto (fun _ : Index => (0 : ℝ)) filter (nhds 0))
  | add first second _ _ firstConvergence secondConvergence =>
    simpa only [ContinuousMap.add_apply,
      integral_add (continuous_integrable _ first) (continuous_integrable _ second)] using
      firstConvergence.add secondConvergence
  | smul scalar function _ convergence =>
    have scalarConvergence : Tendsto (fun _ : Index => scalar) filter (nhds scalar) :=
      tendsto_const_nhds
    simpa only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul] using
      scalarConvergence.mul convergence

/-- Compact-product Stone--Weierstrass upgrades product-test convergence to
the actual weak topology of probability measures. -/
theorem weak_tendsto_of_product_integrals {Index : Type*} {filter : Filter Index}
    (measures : Index → ProbabilityMeasure (Space × Space))
    (limitMeasure : ProbabilityMeasure (Space × Space))
    (productConvergence : ∀ first second : Space →ᵇ ℝ,
      Tendsto (fun index => ∫ pair : Space × Space, first pair.1 * second pair.2
        ∂(measures index : Measure _)) filter
        (nhds (∫ pair : Space × Space, first pair.1 * second pair.2
          ∂(limitMeasure : Measure _)))) :
    Tendsto measures filter (nhds limitMeasure) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro function
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  obtain ⟨approximation, membership, approximationClose⟩ :=
    exists_productSpan_uniform_approximation function.toContinuousMap (epsilon / 4) (by positivity)
  have approximationConvergence := productSpan_integral_tendsto measures limitMeasure
    productConvergence membership
  have eventuallyClose := Metric.tendsto_nhds.mp approximationConvergence
    (epsilon / 2) (by positivity)
  filter_upwards [eventuallyClose] with index middleClose
  have firstClose := integral_difference_le (measures index) function.toContinuousMap approximation
  have lastClose := integral_difference_le limitMeasure approximation function.toContinuousMap
  have reversedClose : ‖function.toContinuousMap - approximation‖ < epsilon / 4 := by
    simpa only [norm_sub_rev] using approximationClose
  rw [dist_eq_norm] at middleClose ⊢
  have triangle := norm_add_le
    ((∫ pair, function pair ∂(measures index : Measure _)) -
      (∫ pair, approximation pair ∂(measures index : Measure _)))
    ((∫ pair, approximation pair ∂(measures index : Measure _)) -
      (∫ pair, approximation pair ∂(limitMeasure : Measure _)) +
      ((∫ pair, approximation pair ∂(limitMeasure : Measure _)) -
        (∫ pair, function pair ∂(limitMeasure : Measure _))))
  have triangleSecond := norm_add_le
    ((∫ pair, approximation pair ∂(measures index : Measure _)) -
      (∫ pair, approximation pair ∂(limitMeasure : Measure _)))
    ((∫ pair, approximation pair ∂(limitMeasure : Measure _)) -
      (∫ pair, function pair ∂(limitMeasure : Measure _)))
  have identity : ((∫ pair, function pair ∂(measures index : Measure _)) -
      (∫ pair, approximation pair ∂(measures index : Measure _))) +
      ((∫ pair, approximation pair ∂(measures index : Measure _)) -
        (∫ pair, approximation pair ∂(limitMeasure : Measure _)) +
        ((∫ pair, approximation pair ∂(limitMeasure : Measure _)) -
          (∫ pair, function pair ∂(limitMeasure : Measure _)))) =
      (∫ pair, function pair ∂(measures index : Measure _)) -
        (∫ pair, function pair ∂(limitMeasure : Measure _)) := by ring
  rw [identity] at triangle
  change ‖(∫ pair, function pair ∂(measures index : Measure _)) -
    (∫ pair, approximation pair ∂(measures index : Measure _))‖ ≤ _ at firstClose
  change ‖(∫ pair, approximation pair ∂(limitMeasure : Measure _)) -
    (∫ pair, function pair ∂(limitMeasure : Measure _))‖ ≤ _ at lastClose
  linarith

end
end IGS.Sec31.StationaryPair

namespace EIGS

open MeasureTheory ProbabilityTheory IGS.Sec31 Filter Topology
open scoped BigOperators NNReal ENNReal Classical ProbabilityTheory BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 4000000

variable {K : ℕ}

def XiNativeStationaryPairWeakKernelProperties (system : EIGSData K)
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
    (normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
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
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass))),
      ∀ _defaultPoint : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair,
      ∃ transition : ℝ≥0 → Kernel
          (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
          (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair),
      ∃ markov : ∀ time, IsMarkovKernel (transition time),
        (∀ (time : ℝ≥0) (values : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
          ∀ᵐ point ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass,
            (∫ location, values location ∂transition time point) =
              QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
                (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
                  distanceRateGreaterThanOne metricEigenpair mass values) point) ∧
        (∀ time, (transition time).Invariant
          (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass)) ∧
        ∀ time : ℝ≥0,
        Tendsto (fun level => xiNativeStationaryPairProbability system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
            lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate normalization
            ratePositive.le normalizationPositive.le level time) atTop
          (nhds (StationaryPair.probability
              (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
                distanceRateGreaterThanOne metricEigenpair mass) (transition time) (markov time)))

theorem xiNativeStationaryPairWeak_kernel_limit (system : EIGSData K)
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
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector))) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
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
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass))),
      ∀ _defaultPoint : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair,
      ∃ transition : ℝ≥0 → Kernel
          (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
          (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair),
      ∃ markov : ∀ time, IsMarkovKernel (transition time),
        (∀ (time : ℝ≥0) (values : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
          ∀ᵐ point ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass,
            (∫ location, values location ∂transition time point) =
              QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
                (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
                  distanceRateGreaterThanOne metricEigenpair mass values) point) ∧
        (∀ time, (transition time).Invariant
          (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass)) ∧
        ∀ time : ℝ≥0,
        Tendsto (fun level => xiNativeStationaryPairProbability system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
            lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate normalization
            ratePositive.le normalizationPositive.le level time) atTop
          (nhds (StationaryPair.probability
              (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
                distanceRateGreaterThanOne metricEigenpair mass) (transition time) (markov time))) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  dsimp only
  intro originalDense defaultPoint
  obtain ⟨transition, markov, representation, invariant, productConvergence⟩ :=
    xiNativeStationaryPairProduct_kernel_limit system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair normalization normalizationPositive normalizedConvergence
      originalDense defaultPoint
  refine ⟨transition, markov, representation, invariant, ?_⟩
  intro time
  exact StationaryPair.weak_tendsto_of_product_integrals _ _ (productConvergence time)

theorem exists_xiNativeStationaryPairWeak_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
        (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      ∃ _originalDense : Dense ((xiContinuousEnergyLpDomain system rulesConnected
        parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
        distanceRateGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive) :
        Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass))),
      XiNativeStationaryPairWeakKernelProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  classical
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
      originalDense, originalNonnegative⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, originalDense, ?_⟩
  exact xiNativeStationaryPairWeak_kernel_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence

end
end EIGS

#print axioms IGS.Sec31.StationaryPair.productAlgebra
#print axioms IGS.Sec31.StationaryPair.productAlgebra_separatesPoints
#print axioms IGS.Sec31.StationaryPair.exists_productSpan_uniform_approximation
#print axioms IGS.Sec31.StationaryPair.productSpan_integral_tendsto
#print axioms IGS.Sec31.StationaryPair.weak_tendsto_of_product_integrals
#print axioms EIGS.XiNativeStationaryPairWeakKernelProperties
#print axioms EIGS.xiNativeStationaryPairWeak_kernel_limit
#print axioms EIGS.exists_xiNativeStationaryPairWeak_of_rules
