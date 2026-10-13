import RequestProject.Section31.EIGSStationaryTwoTimeCorrelations
import RequestProject.Section31.EIGSInvariantMarkovKernelOfRules
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Genuine stationary pair probability measures. Native pair measures use
the actual finite kernel and are pushed forward by the actual completion
embeddings in both coordinates. Limit pair measures use the kernel
constructed from the same actual closed semigroup. Product-test convergence
is derived from the proved stationary correlations; no weak-convergence
premise, moving-start limit, FDD limit, or path-law limit is assumed. -/

namespace IGS.Sec31.StationaryPair

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ProbabilityTheory BoundedContinuousFunction

noncomputable section

variable {Space : Type*} [MeasurableSpace Space]

/-- The genuine joint law of an initial distribution and one kernel
transition. The Markov proof is explicit so families can reuse their proved
Markov witnesses without inserting an instance into a proposition. -/
def probability (measure : ProbabilityMeasure Space) (kernel : Kernel Space Space)
    (markov : IsMarkovKernel kernel) : ProbabilityMeasure (Space × Space) := by
  letI : IsMarkovKernel kernel := markov
  exact ⟨(measure : Measure Space) ⊗ₘ kernel, inferInstance⟩

variable [TopologicalSpace Space] [BorelSpace Space]

theorem integral_product (measure : ProbabilityMeasure Space) (kernel : Kernel Space Space)
    (markov : IsMarkovKernel kernel) (first second : Space →ᵇ ℝ) :
    (∫ pair : Space × Space, first pair.1 * second pair.2 ∂(probability measure kernel markov : Measure _)) =
    ∫ source : Space, first source * (∫ target : Space, second target ∂kernel source) ∂(measure : Measure Space) := by
  letI : IsMarkovKernel kernel := markov
  have integrable : Integrable (fun pair : Space × Space => first pair.1 * second pair.2)
      ((measure : Measure Space) ⊗ₘ kernel) := by
    apply Integrable.of_bound
      (((first.continuous.measurable.comp measurable_fst).mul
        (second.continuous.measurable.comp measurable_snd)).aestronglyMeasurable)
      (‖first‖ * ‖second‖)
    apply Eventually.of_forall
    intro pair
    rw [norm_mul]
    exact mul_le_mul (first.norm_coe_le_norm pair.1) (second.norm_coe_le_norm pair.2)
      (norm_nonneg _) (norm_nonneg _)
  change (∫ pair : Space × Space, first pair.1 * second pair.2 ∂((measure : Measure Space) ⊗ₘ kernel)) = _
  rw [Measure.integral_compProd integrable]
  simp_rw [integral_const_mul]

theorem inner_eq_integral_product (measure : ProbabilityMeasure Space) (kernel : Kernel Space Space)
    (markov : IsMarkovKernel kernel)
    (operator : Lp ℝ 2 (measure : Measure Space) →L[ℝ] Lp ℝ 2 (measure : Measure Space))
    (representation : ∀ function : Space →ᵇ ℝ, ∀ᵐ source ∂(measure : Measure Space),
      (∫ target : Space, function target ∂kernel source) =
        operator (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ function) source)
    (first second : Space →ᵇ ℝ) :
    inner ℝ (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ first)
      (operator (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ second)) =
    ∫ pair : Space × Space, first pair.1 * second pair.2 ∂(probability measure kernel markov : Measure _) := by
  rw [integral_product, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 (measure : Measure Space) ℝ first,
    representation second] with source firstEquality secondEquality
  rw [firstEquality, ← secondEquality]
  exact mul_comm _ _

end
end IGS.Sec31.StationaryPair

namespace EIGS

open MeasureTheory ProbabilityTheory IGS.Sec31 Filter Topology
open scoped BigOperators NNReal ENNReal Classical ProbabilityTheory BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 4000000

variable {K : ℕ} (system : EIGSData K)
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

/-- The actual native stationary joint probability, pushed to the common
completion in both coordinates. -/
def xiNativeStationaryPairProbability (level : ℕ) (time : ℝ≥0) :
    ProbabilityMeasure
      (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair ×
       XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) := by
  let nativePair : ProbabilityMeasure (XiVtx system level × XiVtx system level) :=
    ⟨xiVertexSpeedMeasure system mass level ⊗ₘ
      xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
        rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time, inferInstance⟩
  let pairEmbedding := fun pair : XiVtx system level × XiVtx system level =>
    (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level pair.1,
     xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level pair.2)
  exact nativePair.map (show Measurable pairEmbedding from Measurable.of_discrete).aemeasurable

theorem xiNativeStationaryPairProbability_integral_product (level : ℕ) (time : ℝ≥0)
    (first second : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair →ᵇ ℝ) :
    (∫ pair : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair × XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, first pair.1 * second pair.2 ∂
      (xiNativeStationaryPairProbability system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate normalization
        rateNonnegative normalizationNonnegative level time : Measure _)) =
    ∫ source : XiVtx system level,
      first (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level source) *
      (∫ target : XiVtx system level,
        second (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level target) ∂
        xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
          rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source)
        ∂xiVertexSpeedMeasure system mass level := by
  change (∫ pair : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair × XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, first pair.1 * second pair.2 ∂
    (xiVertexSpeedMeasure system mass level ⊗ₘ
      xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
        rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time).map
      (fun pair : XiVtx system level × XiVtx system level =>
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level pair.1,
         xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level pair.2))) = _
  have productMeasurable : Measurable (fun pair :
      XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair ×
      XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair => first pair.1 * second pair.2) :=
    (first.continuous.measurable.comp measurable_fst).mul
      (second.continuous.measurable.comp measurable_snd)
  rw [integral_map Measurable.of_discrete.aemeasurable productMeasurable.aestronglyMeasurable,
    Measure.integral_compProd Integrable.of_finite]
  simp_rw [integral_const_mul]

theorem xiNativeStationaryPairProduct_kernel_limit (system : EIGSData K)
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
        ∀ (time : ℝ≥0)
          (first second : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair →ᵇ ℝ),
        Tendsto (fun level => ∫ pair : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair × XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, first pair.1 * second pair.2 ∂
          (xiNativeStationaryPairProbability system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
            lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate normalization
            ratePositive.le normalizationPositive.le level time : Measure _)) atTop
          (nhds (∫ pair : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair × XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, first pair.1 * second pair.2 ∂
            (StationaryPair.probability
              (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
                distanceRateGreaterThanOne metricEigenpair mass) (transition time) (markov time) : Measure _))) := by
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
  dsimp only
  intro originalDense defaultPoint
  have kernelProperties := xiInvariantMarkovKernelProperties_of_dense_core system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne
    metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair originalDense
  dsimp only [XiInvariantMarkovKernelProperties] at kernelProperties
  obtain ⟨kernelDensity, kernelForDefault⟩ := kernelProperties
  obtain ⟨transition, markov, representation, invariant⟩ := kernelForDefault defaultPoint
  refine ⟨transition, markov, representation, invariant, ?_⟩
  intro time first second
  have correlation := xiNativeStationaryContinuousCorrelation_limit system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne
    metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense time first second
  have productConvergence : Tendsto (fun level => ∫ pair : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair × XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, first pair.1 * second pair.2 ∂
      (xiNativeStationaryPairProbability system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate normalization
        ratePositive.le normalizationPositive.le level time : Measure _)) atTop
      (nhds (inner ℝ (core.embed first)
        (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense
          time (core.embed second)))) := by
    simpa only [xiNativeStationaryPairProbability_integral_product] using correlation
  have targetIdentity : inner ℝ (core.embed first)
      (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense
        time (core.embed second)) =
      ∫ pair : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair × XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, first pair.1 * second pair.2 ∂
        (StationaryPair.probability
          (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass) (transition time) (markov time) : Measure _) := by
    apply StationaryPair.inner_eq_integral_product
    intro function
    simpa only [xiContinuousL2Map, ContinuousMap.toLp_comp_toContinuousMap] using
      representation time function.toContinuousMap
  simpa only [targetIdentity] using productConvergence

theorem exists_xiNativeStationaryPairProduct_of_rules (system : EIGSData K)
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
      let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive
      let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
        intro sequence energyCauchy ambientZero
        exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
          mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
          (by simpa using ambientZero.norm)
      ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass))),
      ∀ _defaultPoint : XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
        (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair,
      ∃ transition : ℝ≥0 → Kernel
          (XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
            (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair)
          (XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
            (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair),
      ∃ markov : ∀ time, IsMarkovKernel (transition time),
        (∀ (time : ℝ≥0) (values : C(XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
            (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair, ℝ)),
          ∀ᵐ point ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
              distanceRateGreaterThanOne parameters.eigenpair mass,
            (∫ location, values location ∂transition time point) =
              QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
                (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
                  distanceRateGreaterThanOne parameters.eigenpair mass values) point) ∧
        (∀ time, (transition time).Invariant
          (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
            distanceRateGreaterThanOne parameters.eigenpair mass)) ∧
        ∀ (time : ℝ≥0)
          (first second : XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
            (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair →ᵇ ℝ),
        Tendsto (fun level => ∫ pair : XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair × XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair, first pair.1 * second pair.2 ∂
          (xiNativeStationaryPairProbability system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
            parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass resistanceRate normalization
            ratePositive.le normalizationPositive.le level time : Measure _)) atTop
          (nhds (∫ pair : XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair × XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair, first pair.1 * second pair.2 ∂
            (StationaryPair.probability
              (xiLimitProbabilityMeasure system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
                distanceRateGreaterThanOne parameters.eigenpair mass) (transition time) (markov time) : Measure _))) := by
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
  exact xiNativeStationaryPairProduct_kernel_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense


end
end EIGS

#print axioms IGS.Sec31.StationaryPair.probability
#print axioms IGS.Sec31.StationaryPair.integral_product
#print axioms IGS.Sec31.StationaryPair.inner_eq_integral_product
#print axioms EIGS.xiNativeStationaryPairProbability
#print axioms EIGS.xiNativeStationaryPairProbability_integral_product

#print axioms EIGS.xiNativeStationaryPairProduct_kernel_limit

#print axioms EIGS.exists_xiNativeStationaryPairProduct_of_rules
