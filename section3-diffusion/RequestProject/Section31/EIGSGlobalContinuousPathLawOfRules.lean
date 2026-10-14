import RequestProject.Section31.EIGSCompatibleFiniteHorizonLawsOfRules
import RequestProject.Section31.IntegerHorizonCompatiblePathLaw

/-! One probability on continuous nonnegative-real-time paths for every
starting point of the actual limit space, with the same semigroup kernel
finite observations as the compatible finite-horizon limits. The measurable
space is induced by evaluations. Identification with the Borel sigma algebra
of the topology of uniform convergence on compact time intervals, measurability
in the starting point, and the Hunt property are not asserted here. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped UniformConvergence NNReal Classical BigOperators
noncomputable section
set_option maxHeartbeats 5000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]

theorem continuousTimePathLaw_ordered_integral_eq_local
    (rates : ℕ → ℝ≥0) (embedding : (level : ℕ) → Vertex level → State)
    (laws : (horizon : ℕ) → ProbabilityMeasure
      (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding)))
    (globalLaw : ProbabilityMeasure (ContinuousTimePath State))
    (finiteEvaluations : ∀ (horizon dimension : ℕ) (times : Fin dimension → ℝ≥0)
      (timesInHorizon : ∀ index, (times index : ℝ) ≤ horizon),
      (globalLaw : Measure (ContinuousTimePath State)).map (fun path => fun index => path.val (times index)) =
        (laws horizon : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding))).map (fun path => fun index => UniformFun.toFun path.val
          ⟨(times index : ℝ), (times index).property, timesInHorizon index⟩))
    (horizon : ℕ) (times : ℕ → ℝ≥0) (timesMonotone : Monotone times)
    (tests : ℕ → C(State, ℝ)) (count : ℕ) (terminal : C(State, ℝ))
    (timesInHorizon : (times count : ℝ) ≤ horizon) :
    (∫ path : ContinuousTimePath State, (∏ index : Fin count, tests index.val (path.val (times index.val))) *
      terminal (path.val (times count)) ∂(globalLaw : Measure (ContinuousTimePath State))) =
      ∫ path : FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding), (∏ index : Fin count, tests index.val (UniformFun.toFun path.val
        ⟨(times index.val : ℝ), (times index.val).property,
          by exact_mod_cast ((timesMonotone (Nat.le_of_lt index.isLt)).trans
            (show times count ≤ (horizon : ℝ≥0) by exact_mod_cast timesInHorizon))⟩)) *
        terminal (UniformFun.toFun path.val
          ⟨(times count : ℝ), (times count).property, timesInHorizon⟩)
          ∂(laws horizon : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding))) := by
  let observation : (Fin (count + 1) → State) → ℝ := fun values =>
    (∏ index : Fin count, tests index.val (values index.castSucc)) *
      terminal (values (Fin.last count))
  have observationContinuous : Continuous observation :=
    (continuous_finset_prod Finset.univ fun index _ =>
      (tests index.val).continuous.comp (continuous_apply index.castSucc)).mul
        (terminal.continuous.comp (continuous_apply (Fin.last count)))
  have globalEvaluationMeasurable : Measurable (fun path : ContinuousTimePath State =>
      fun index : Fin (count + 1) => path.val (times index.val)) :=
    measurable_pi_lambda _ fun index =>
      (measurable_pi_apply (times index.val)).comp measurable_subtype_coe
  have allTimesInHorizon (index : Fin (count + 1)) : (times index.val : ℝ) ≤ horizon := by
    exact_mod_cast ((timesMonotone (Nat.le_of_lt_succ index.isLt)).trans
      (show times count ≤ (horizon : ℝ≥0) by exact_mod_cast timesInHorizon))
  have localEvaluationMeasurable : Measurable (fun path :
      FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding) =>
      fun index : Fin (count + 1) => UniformFun.toFun path.val
        ⟨(times index.val : ℝ), (times index.val).property, allTimesInHorizon index⟩) :=
    measurable_pi_lambda _ fun index =>
      (finiteSupportPathSpace_continuous_eval
        (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding)
        ⟨(times index.val : ℝ), (times index.val).property, allTimesInHorizon index⟩).measurable
  have integralIdentity := congrArg (fun measure : Measure (Fin (count + 1) → State) =>
      ∫ values, observation values ∂measure)
    (finiteEvaluations horizon (count + 1) (fun index => times index.val) allTimesInHorizon)
  dsimp only at integralIdentity
  rw [integral_map globalEvaluationMeasurable.aemeasurable
      observationContinuous.measurable.aestronglyMeasurable,
    integral_map localEvaluationMeasurable.aemeasurable
      observationContinuous.measurable.aestronglyMeasurable] at integralIdentity
  simpa only [observation, Fin.val_castSucc, Fin.val_last] using integralIdentity

end
end IGS.Sec31.DiscreteMarkov

namespace EIGS

open IGS.Sec31 MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical BigOperators NNReal UniformConvergence BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}
def XiGlobalContinuousPathLawProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
    normalization normalizationPositive
  let paths := fun horizon => finiteHorizonStepPaths horizon rates parameters.vertexEmbedding
  ∃ semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ),
    (∀ time, ‖semigroup time‖ ≤ 1) ∧
    semigroup 0 = ContinuousLinearMap.id ℝ C(parameters.LimitSpace, ℝ) ∧
    (∀ firstTime secondTime, semigroup (firstTime + secondTime) =
      (semigroup firstTime).comp (semigroup secondTime)) ∧
    Continuous (fun point : C(parameters.LimitSpace, ℝ) × ℝ≥0 => semigroup point.2 point.1) ∧
    (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
      Tendsto (fun level => ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time
        (fun vertex => function (parameters.vertexEmbedding level vertex)) -
        (fun vertex => semigroup time function (parameters.vertexEmbedding level vertex))‖) atTop (𝓝 0)) ∧
    ∃ positive : ∀ time (function : C(parameters.LimitSpace, ℝ)),
      (∀ point, 0 ≤ function point) → ∀ point, 0 ≤ semigroup time function point,
    ∃ preservesOne : ∀ time, semigroup time 1 = 1,
      ∀ start : parameters.LimitSpace,
        ∃ starts : ∀ level, XiVtx system level,
          Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start) ∧
          ∃ laws : (horizon : ℝ≥0) → ProbabilityMeasure (FiniteSupportPathSpace (paths horizon)),
            (∀ horizon, Tendsto (fun level => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding
              (fun level => xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
              (fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level))) level)
                atTop (𝓝 (laws horizon))) ∧
            (∀ horizon, ∀ᵐ path ∂(laws horizon : Measure (FiniteSupportPathSpace (paths horizon))),
              Continuous (UniformFun.toFun path.val)) ∧
            (∀ (shortHorizon longHorizon : ℝ≥0) (horizonsOrdered : shortHorizon ≤ longHorizon),
              (laws longHorizon).map
                (finiteHorizonPathRestriction_continuous shortHorizon longHorizon horizonsOrdered
                  rates parameters.vertexEmbedding).measurable.aemeasurable = laws shortHorizon) ∧
            ∃ globalLaw : ProbabilityMeasure (ContinuousTimePath parameters.LimitSpace),
              (∀ (horizon dimension : ℕ) (times : Fin dimension → ℝ≥0)
                (timesInHorizon : ∀ index, (times index : ℝ) ≤ horizon),
                (globalLaw : Measure (ContinuousTimePath parameters.LimitSpace)).map (fun path => fun index => path.val (times index)) =
                  (laws (horizon : ℝ≥0) : Measure (FiniteSupportPathSpace (paths (horizon : ℝ≥0)))).map (fun path => fun index => UniformFun.toFun path.val
                    ⟨(times index : ℝ), (times index).property, timesInHorizon index⟩)) ∧
              ∀ (times : ℕ → ℝ≥0) (timesMonotone : Monotone times), times 0 = 0 →
                ∀ (tests : ℕ → C(parameters.LimitSpace, ℝ)) (count : ℕ)
                  (terminal : C(parameters.LimitSpace, ℝ)),
                  (∫ path : ContinuousTimePath parameters.LimitSpace, (∏ index : Fin count, tests index.val (path.val (times index.val))) *
                    terminal (path.val (times count)) ∂(globalLaw : Measure (ContinuousTimePath parameters.LimitSpace))) =
                    ContinuousMarkov.kernelBackwardProduct
                      (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
                      ((List.range count).map (fun index => (times (index + 1) - times index, tests index)))
                      terminal start
theorem xiGlobalContinuousPathLawProperties_of_compatible (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate normalization : ℝ) (normalizationPositive : 0 < normalization)
    (compatibleProperties : XiCompatibleFiniteHorizonLawsProperties system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive) :
    XiGlobalContinuousPathLawProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
    normalization normalizationPositive
  dsimp only [XiCompatibleFiniteHorizonLawsProperties, XiGlobalContinuousPathLawProperties]
    at compatibleProperties ⊢
  obtain ⟨semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    supLimit, positive, preservesOne, compatibleLimits⟩ := compatibleProperties
  refine ⟨semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    supLimit, positive, preservesOne, ?_⟩
  intro start
  letI : Nonempty parameters.LimitSpace := ⟨start⟩
  obtain ⟨starts, startsConverge, laws, lawsConverge, lawsContinuous, lawsCompatible,
    lawsObservations⟩ := compatibleLimits start
  obtain ⟨globalLaw, finiteEvaluations⟩ :=
    exists_continuousTimePathLaw_of_compatible_integer_horizons rates parameters.vertexEmbedding
      (fun horizon : ℕ => laws (horizon : ℝ≥0))
      (by
        intro shortHorizon longHorizon ordered
        exact lawsCompatible (shortHorizon : ℝ≥0) (longHorizon : ℝ≥0) (by exact_mod_cast ordered))
      (fun horizon => lawsContinuous (horizon : ℝ≥0))
  refine ⟨starts, startsConverge, laws, lawsConverge, lawsContinuous, lawsCompatible,
    globalLaw, finiteEvaluations, ?_⟩
  intro times timesMonotone startsAtZero tests count terminal
  have transfer := continuousTimePathLaw_ordered_integral_eq_local rates parameters.vertexEmbedding
    (fun horizon : ℕ => laws (horizon : ℝ≥0)) globalLaw finiteEvaluations
    (integerHorizonAbove (times count)) times timesMonotone tests count terminal
    (time_le_integerHorizonAbove (times count))
  exact transfer.trans (lawsObservations (integerHorizonAbove (times count) : ℝ≥0)
    times timesMonotone startsAtZero tests count terminal
    (by exact_mod_cast time_le_integerHorizonAbove (times count)))
theorem exists_xiGlobalContinuousPathLaw_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      XiGlobalContinuousPathLawProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, compatibleProperties⟩ :=
    exists_xiCompatibleFiniteHorizonLaws_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence,
    xiGlobalContinuousPathLawProperties_of_compatible system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive compatibleProperties⟩

end
end EIGS

#print axioms IGS.Sec31.DiscreteMarkov.continuousTimePathLaw_ordered_integral_eq_local
#print axioms EIGS.xiGlobalContinuousPathLawProperties_of_compatible
#print axioms EIGS.exists_xiGlobalContinuousPathLaw_of_rules


