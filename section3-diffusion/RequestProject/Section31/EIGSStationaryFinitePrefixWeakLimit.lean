import RequestProject.Section31.EIGSStationaryFiniteObservations
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! Genuine weak convergence of fixed-step stationary finite-prefix laws.
Finite-coordinate product-test density is proved by Stone--Weierstrass, and
all native products come from the accepted actual path-observation theorem.
No unequal-gap or infinite-path weak convergence is asserted. -/

namespace IGS.Sec31.FiniteProductWeak

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 4000000

variable {Coordinates Space : Type*} [Fintype Coordinates] [MetricSpace Space] [CompactSpace Space]

def productTest (tests : Coordinates → C(Space, ℝ)) : C(Coordinates → Space, ℝ) where
  toFun point := ∏ coordinate, tests coordinate (point coordinate)
  continuous_toFun := by
    apply continuous_finset_prod
    intro coordinate _
    exact (tests coordinate).continuous.comp (continuous_apply coordinate)

def productSpan : Submodule ℝ C(Coordinates → Space, ℝ) :=
  Submodule.span ℝ (Set.range (productTest (Coordinates := Coordinates) (Space := Space)))

omit [CompactSpace Space] in
 theorem productTest_mem (tests : Coordinates → C(Space, ℝ)) :
    productTest tests ∈ (productSpan : Submodule ℝ C(Coordinates → Space, ℝ)) :=
  Submodule.subset_span ⟨tests, rfl⟩

def productAlgebra : Subalgebra ℝ C(Coordinates → Space, ℝ) where
  carrier := {function | function ∈ (productSpan : Submodule ℝ C(Coordinates → Space, ℝ))}
  zero_mem' := (productSpan).zero_mem
  add_mem' := (productSpan).add_mem
  one_mem' := by
    have identity : productTest (fun _ : Coordinates => (1 : C(Space, ℝ))) = 1 := by
      ext point
      simp [productTest]
    rw [← identity]
    exact productTest_mem _
  algebraMap_mem' scalar := by
    have identity : productTest (fun _ : Coordinates => (1 : C(Space, ℝ))) = 1 := by
      ext point
      simp [productTest]
    rw [Algebra.algebraMap_eq_smul_one, ← identity]
    exact (productSpan).smul_mem scalar (productTest_mem _)
  mul_mem' := by
    intro first second firstMem secondMem
    change first * second ∈ (productSpan : Submodule ℝ C(Coordinates → Space, ℝ))
    apply Submodule.span_induction₂ (p := fun first second _ _ =>
      first * second ∈ (productSpan : Submodule ℝ C(Coordinates → Space, ℝ)))
      (s := Set.range (productTest (Coordinates := Coordinates) (Space := Space)))
      (t := Set.range (productTest (Coordinates := Coordinates) (Space := Space)))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ firstMem secondMem
    · intro first second firstMem secondMem
      obtain ⟨firstTests, rfl⟩ := firstMem
      obtain ⟨secondTests, rfl⟩ := secondMem
      have identity : productTest firstTests * productTest secondTests =
          productTest (fun coordinate => firstTests coordinate * secondTests coordinate) := by
        ext point
        exact (Finset.prod_mul_distrib).symm
      rw [identity]
      exact productTest_mem _
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
    (productAlgebra : Subalgebra ℝ C(Coordinates → Space, ℝ)).SeparatesPoints := by
  classical
  intro first second different
  have coordinateDifferent : ∃ coordinate, first coordinate ≠ second coordinate := by
    by_contra none
    apply different
    funext coordinate
    exact not_ne_iff.mp (not_exists.mp none coordinate)
  obtain ⟨coordinate, coordinateDifferent⟩ := coordinateDifferent
  let distanceTest : C(Space, ℝ) :=
    ⟨fun point => dist point (first coordinate), continuous_id.dist continuous_const⟩
  let tests : Coordinates → C(Space, ℝ) :=
    fun index => if index = coordinate then distanceTest else 1
  have productEvaluation (point : Coordinates → Space) :
      productTest tests point = dist (point coordinate) (first coordinate) := by
    have factor (index : Coordinates) : tests index (point index) =
        if index = coordinate then dist (point coordinate) (first coordinate) else 1 := by
      by_cases same : index = coordinate
      · subst index
        simp [tests, distanceTest]
      · simp only [tests, if_neg same, ContinuousMap.one_apply]
    change (∏ index, tests index (point index)) = _
    simp_rw [factor]
    simp
  refine ⟨productTest tests, ⟨productTest tests, productTest_mem _, rfl⟩, ?_⟩
  intro equality
  apply coordinateDifferent
  have zeroDistance : dist (second coordinate) (first coordinate) = 0 := by
    rw [productEvaluation first, productEvaluation second, dist_self] at equality
    exact equality.symm
  exact (dist_eq_zero.mp zeroDistance).symm

theorem exists_productSpan_uniform_approximation (function : C(Coordinates → Space, ℝ))
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ approximation ∈ (productSpan : Submodule ℝ C(Coordinates → Space, ℝ)),
      ‖approximation - function‖ < epsilon := by
  obtain ⟨approximation, close⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      (productAlgebra : Subalgebra ℝ C(Coordinates → Space, ℝ))
      productAlgebra_separatesPoints function epsilon positive
  exact ⟨approximation, approximation.property, close⟩

variable [MeasurableSpace Space] [BorelSpace Space]

theorem continuous_integrable (measure : ProbabilityMeasure (Coordinates → Space))
    (function : C(Coordinates → Space, ℝ)) :
    Integrable function (measure : Measure (Coordinates → Space)) := by
  exact Integrable.of_bound function.continuous.measurable.aestronglyMeasurable
    ‖function‖ (Eventually.of_forall function.norm_coe_le_norm)

theorem integral_difference_le (measure : ProbabilityMeasure (Coordinates → Space))
    (first second : C(Coordinates → Space, ℝ)) :
    ‖(∫ point, first point ∂(measure : Measure _)) -
      (∫ point, second point ∂(measure : Measure _))‖ ≤ ‖first - second‖ := by
  rw [← integral_sub (continuous_integrable measure first) (continuous_integrable measure second)]
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := (measure : Measure (Coordinates → Space)))
      (Eventually.of_forall (first - second).norm_coe_le_norm))

theorem productSpan_integral_tendsto {Index : Type*} {filter : Filter Index}
    (measures : Index → ProbabilityMeasure (Coordinates → Space))
    (limitMeasure : ProbabilityMeasure (Coordinates → Space))
    (productConvergence : ∀ tests : Coordinates → Space →ᵇ ℝ,
      Tendsto (fun index => ∫ point : Coordinates → Space, ∏ coordinate, tests coordinate (point coordinate)
        ∂(measures index : Measure _)) filter
        (nhds (∫ point : Coordinates → Space, ∏ coordinate, tests coordinate (point coordinate)
          ∂(limitMeasure : Measure _))))
    {function : C(Coordinates → Space, ℝ)} (membership : function ∈ productSpan) :
    Tendsto (fun index => ∫ pair, function pair ∂(measures index : Measure _)) filter
      (nhds (∫ pair, function pair ∂(limitMeasure : Measure _))) := by
  induction membership using Submodule.span_induction with
  | mem function membership =>
    obtain ⟨tests, rfl⟩ := membership
    simpa only [productTest,
      ContinuousMap.linearIsometryBoundedOfCompact_apply_apply] using
      productConvergence (fun coordinate =>
        ContinuousMap.linearIsometryBoundedOfCompact Space ℝ ℝ (tests coordinate))
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
    (measures : Index → ProbabilityMeasure (Coordinates → Space))
    (limitMeasure : ProbabilityMeasure (Coordinates → Space))
    (productConvergence : ∀ tests : Coordinates → Space →ᵇ ℝ,
      Tendsto (fun index => ∫ point : Coordinates → Space, ∏ coordinate, tests coordinate (point coordinate)
        ∂(measures index : Measure _)) filter
        (nhds (∫ point : Coordinates → Space, ∏ coordinate, tests coordinate (point coordinate)
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
end IGS.Sec31.FiniteProductWeak

namespace IGS.Sec31.FixedStepPrefixWeak

open MeasureTheory ProbabilityTheory Preorder Filter Topology
open scoped BigOperators BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 4000000

def prefixIndexEquiv (count : ℕ) : Fin (count + 1) ≃ Finset.Iic count where
  toFun index := ⟨index.val, Finset.mem_Iic.mpr (Nat.le_of_lt_succ index.isLt)⟩
  invFun index := ⟨index.val, Nat.lt_succ_of_le (Finset.mem_Iic.mp index.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem prefix_prod_split (count : ℕ) (values : Finset.Iic count → ℝ) :
    (∏ index, values index) =
      (∏ index : Fin count, values ⟨index.val, Finset.mem_Iic.mpr (Nat.le_of_lt index.isLt)⟩) *
        values ⟨count, Finset.mem_Iic.mpr le_rfl⟩ := by
  calc
    _ = ∏ index : Fin (count + 1), values (prefixIndexEquiv count index) :=
      (Equiv.prod_comp (prefixIndexEquiv count) values).symm
    _ = _ := by
      rw [Fin.prod_univ_castSucc]
      rfl

def extendTests {Test : Type*} [One Test] (count : ℕ)
    (tests : Finset.Iic count → Test) (index : ℕ) : Test :=
  if bound : index ≤ count then tests ⟨index, Finset.mem_Iic.mpr bound⟩ else 1

variable {X Space : Type*} [MeasurableSpace X]
    [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]

omit [MeasurableSpace X] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space] in
theorem path_coordinateProduct_eq_prefix (count : ℕ) (embedding : X → Space)
    (tests : Finset.Iic count → Space →ᵇ ℝ) (path : ℕ → X) :
    (∏ index : Finset.Iic count, tests index (embedding (path index.val))) =
      (∏ index : Fin count, extendTests count tests index.val (embedding (path index.val))) *
        tests ⟨count, Finset.mem_Iic.mpr le_rfl⟩ (embedding (path count)) := by
  classical
  rw [prefix_prod_split]
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  simp only [extendTests, dif_pos (Nat.le_of_lt index.isLt)]

def mappedProbability (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (embedding : X → Space) (measurable : Measurable embedding)
    (count : ℕ) : ProbabilityMeasure (Finset.Iic count → Space) :=
  (DiscreteMarkov.finitePrefixProbability kernel initial count).map
    (show Measurable (fun history : Finset.Iic count → X => fun index => embedding (history index)) from
      measurable_pi_lambda _ (fun index => measurable.comp (measurable_pi_apply index))).aemeasurable

omit [CompactSpace Space] in
theorem mappedProbability_integral_product (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (embedding : X → Space) (measurable : Measurable embedding)
    (count : ℕ) (tests : Finset.Iic count → Space →ᵇ ℝ) :
    (∫ history : Finset.Iic count → Space, ∏ index, tests index (history index)
      ∂(mappedProbability kernel initial embedding measurable count : Measure _)) =
      ∫ path, (∏ index : Fin count, extendTests count tests index.val (embedding (path index.val))) *
        tests ⟨count, Finset.mem_Iic.mpr le_rfl⟩ (embedding (path count))
        ∂DiscreteMarkov.pathLaw kernel (initial : Measure X) := by
  have productMeasurable : Measurable (fun history : Finset.Iic count → Space =>
      ∏ index, tests index (history index)) := by
    apply Finset.measurable_prod
    intro index _
    exact (tests index).continuous.measurable.comp (measurable_pi_apply index)
  have pulledMeasurable : Measurable (fun history : Finset.Iic count → X =>
      ∏ index, tests index (embedding (history index))) := by
    apply Finset.measurable_prod
    intro index _
    exact (tests index).continuous.measurable.comp (measurable.comp (measurable_pi_apply index))
  change (∫ history : Finset.Iic count → Space, ∏ index, tests index (history index)
    ∂(DiscreteMarkov.finitePrefixProbability kernel initial count : Measure _).map
      (fun history : Finset.Iic count → X => fun index => embedding (history index))) = _
  rw [integral_map (show Measurable (fun history : Finset.Iic count → X =>
    fun index => embedding (history index)) from
      measurable_pi_lambda _ (fun index => measurable.comp (measurable_pi_apply index))).aemeasurable
    productMeasurable.aestronglyMeasurable]
  change (∫ history : Finset.Iic count → X, ∏ index, tests index (embedding (history index))
    ∂(DiscreteMarkov.pathLaw kernel (initial : Measure X)).map (frestrictLe count)) = _
  rw [integral_map (measurable_frestrictLe count).aemeasurable pulledMeasurable.aestronglyMeasurable]
  simp_rw [frestrictLe_apply, path_coordinateProduct_eq_prefix]

omit [CompactSpace Space] in
theorem finitePrefixProbability_integral_product (kernel : Kernel Space Space) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure Space) (count : ℕ) (tests : Finset.Iic count → Space →ᵇ ℝ) :
    (∫ history : Finset.Iic count → Space, ∏ index, tests index (history index)
      ∂(DiscreteMarkov.finitePrefixProbability kernel initial count : Measure _)) =
      ∫ path, (∏ index : Fin count, extendTests count tests index.val (path index.val)) *
        tests ⟨count, Finset.mem_Iic.mpr le_rfl⟩ (path count)
        ∂DiscreteMarkov.pathLaw kernel (initial : Measure Space) := by
  have productMeasurable : Measurable (fun history : Finset.Iic count → Space =>
      ∏ index, tests index (history index)) := by
    apply Finset.measurable_prod
    intro index _
    exact (tests index).continuous.measurable.comp (measurable_pi_apply index)
  change (∫ history : Finset.Iic count → Space, ∏ index, tests index (history index)
    ∂(DiscreteMarkov.pathLaw kernel (initial : Measure Space)).map (frestrictLe count)) = _
  rw [integral_map (measurable_frestrictLe count).aemeasurable productMeasurable.aestronglyMeasurable]
  have split (path : ℕ → Space) := path_coordinateProduct_eq_prefix count (id : Space → Space) tests path
  exact integral_congr_ae (Eventually.of_forall split)

end
end IGS.Sec31.FixedStepPrefixWeak

namespace EIGS

open MeasureTheory ProbabilityTheory IGS.Sec31 Filter Topology
open scoped BigOperators NNReal ENNReal Classical BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

def xiNativeStationaryPrefixProbability (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system) (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (level : ℕ) (step : ℝ≥0) (count : ℕ) :
    ProbabilityMeasure (Finset.Iic count → XiMetricCompletion system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :=
  FixedStepPrefixWeak.mappedProbability
    (xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative step)
    (xiNativeSpeedProbabilityMeasure system mass level)
    (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level)
    (measurable_xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair level) count

def XiNativeStationaryFixedStepPrefixWeakProperties (system : EIGSData K)
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
        ∀ (step : ℝ≥0) (count : ℕ),
        Tendsto (fun level => xiNativeStationaryPrefixProbability system rulesConnected
          rulesLoopless rulesUnique plantingNonadjacent lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass resistanceRate normalization
          ratePositive.le normalizationPositive.le level step count) atTop
          (nhds (DiscreteMarkov.finitePrefixProbability (transition step)
            (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass) count))

theorem xiNativeStationaryFixedStepPrefix_weak_limit (system : EIGSData K)
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
    XiNativeStationaryFixedStepPrefixWeakProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair normalization normalizationPositive := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  have previous := xiNativeStationaryFixedStepObservations_limit system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive normalizedConvergence
  dsimp only [XiNativeStationaryFixedStepObservationProperties] at previous
  dsimp only [XiNativeStationaryFixedStepPrefixWeakProperties]
  intro originalDense defaultPoint
  obtain ⟨transition, markov, representation, invariant, productConvergence⟩ := previous originalDense defaultPoint
  refine ⟨transition, markov, representation, invariant, ?_⟩
  intro step count
  letI : IsMarkovKernel (transition step) := markov step
  apply FiniteProductWeak.weak_tendsto_of_product_integrals
  intro tests
  have convergence := productConvergence step (FixedStepPrefixWeak.extendTests count tests)
    count (tests ⟨count, Finset.mem_Iic.mpr le_rfl⟩)
  simpa only [xiNativeStationaryPrefixProbability,
    FixedStepPrefixWeak.mappedProbability_integral_product,
    FixedStepPrefixWeak.finitePrefixProbability_integral_product,
    xiNativeSpeedProbabilityMeasure, xiLimitProbabilityMeasure] using convergence

theorem exists_xiNativeStationaryFixedStepPrefixWeak_of_rules (system : EIGSData K)
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
      XiNativeStationaryFixedStepPrefixWeakProperties system rulesConnected rulesLoopless rulesUnique
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
  exact xiNativeStationaryFixedStepPrefix_weak_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence



end
end EIGS

#print axioms IGS.Sec31.FiniteProductWeak.productAlgebra
#print axioms IGS.Sec31.FiniteProductWeak.productAlgebra_separatesPoints
#print axioms IGS.Sec31.FiniteProductWeak.exists_productSpan_uniform_approximation
#print axioms IGS.Sec31.FiniteProductWeak.productSpan_integral_tendsto
#print axioms IGS.Sec31.FiniteProductWeak.weak_tendsto_of_product_integrals
#print axioms IGS.Sec31.FixedStepPrefixWeak.mappedProbability
#print axioms IGS.Sec31.FixedStepPrefixWeak.mappedProbability_integral_product
#print axioms IGS.Sec31.FixedStepPrefixWeak.finitePrefixProbability_integral_product
#print axioms EIGS.xiNativeStationaryPrefixProbability
#print axioms EIGS.XiNativeStationaryFixedStepPrefixWeakProperties
#print axioms EIGS.xiNativeStationaryFixedStepPrefix_weak_limit
#print axioms EIGS.exists_xiNativeStationaryFixedStepPrefixWeak_of_rules
