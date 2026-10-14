import RequestProject.Section31.EIGSDeterministicMarkovContinuousPathOfRules
import RequestProject.Section31.ContinuousPathStoppingConditionalExpectation

/-! The actual five-rule construction has the continuous-test Markov identity
at every everywhere finite stopping time in the canonical natural filtration.
The semigroup, its native uniform approximation, and all path laws remain the
same witnesses as in the deterministic-time construction. Both event-integral
and conditional-expectation identities are derived internally. Borel tests,
usual augmentation, path-future identities, and a full Hunt assertion remain
separate and are not claimed here. -/

namespace EIGS

open IGS.Sec31 MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical BigOperators NNReal UniformConvergence BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}
def XiFiniteStoppingContinuousPathProperties (system : EIGSData K)
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
  letI xiFiniteStoppingPropertiesLimitCompactSpace : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI xiFiniteStoppingPropertiesLimitMeasurableSpace : MeasurableSpace parameters.LimitSpace := borel _
  letI xiFiniteStoppingPropertiesLimitBorelSpace : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI xiFiniteStoppingPropertiesPathMeasurableSpace : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
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
      ∃ globalLaws : parameters.LimitSpace → ProbabilityMeasure C(ℝ≥0, parameters.LimitSpace),
        ∃ familyMeasurable : Measurable (fun start =>
          (globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))),
          Measurable globalLaws ∧
          IsMarkovKernel (continuousPathFamilyKernel globalLaws familyMeasurable) ∧
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
              ((globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace)).map (fun path => path 0) = Measure.dirac start) ∧
              (∀ (horizon dimension : ℕ) (times : Fin dimension → ℝ≥0)
                (timesInHorizon : ∀ index, (times index : ℝ) ≤ horizon),
                (globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace)).map (fun path => fun index => path (times index)) =
                  (laws (horizon : ℝ≥0) : Measure (FiniteSupportPathSpace (paths (horizon : ℝ≥0)))).map
                    (fun path => fun index => UniformFun.toFun path.val
                    ⟨(times index : ℝ), (times index).property, timesInHorizon index⟩)) ∧
              (∀ (times : ℕ → ℝ≥0) (timesMonotone : Monotone times), times 0 = 0 →
                ∀ (tests : ℕ → C(parameters.LimitSpace, ℝ)) (count : ℕ)
                  (terminal : C(parameters.LimitSpace, ℝ)),
                  (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) *
                    terminal (path (times count)) ∂(globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))) =
                    ContinuousMarkov.kernelBackwardProduct
                      (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
                      ((List.range count).map (fun index => (times (index + 1) - times index, tests index)))
                      terminal start) ∧
              (∀ (time delay : ℝ≥0) (terminal : C(parameters.LimitSpace, ℝ))
                (event : Set C(ℝ≥0, parameters.LimitSpace)),
                MeasurableSet[canonicalContinuousPathFiltration (State := parameters.LimitSpace) time] event →
                (∫ path in event, terminal (path (time + delay))
                  ∂(globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))) =
                  ∫ path in event, semigroup delay terminal (path time)
                    ∂(globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))) ∧
              ∀ (stoppingTime : C(ℝ≥0, parameters.LimitSpace) → ℝ≥0)
                (stopping : IsStoppingTime canonicalContinuousPathFiltration
                  (fun path => (stoppingTime path : WithTop ℝ≥0)))
                (delay : ℝ≥0) (terminal : C(parameters.LimitSpace, ℝ)),
                (∀ event : Set C(ℝ≥0, parameters.LimitSpace),
                  MeasurableSet[stopping.measurableSpace] event →
                  (∫ path in event, terminal (path (stoppingTime path + delay))
                    ∂(globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))) =
                    ∫ path in event, semigroup delay terminal (path (stoppingTime path))
                      ∂(globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))) ∧
                MeasureTheory.condExp stopping.measurableSpace
                    (globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))
                    (fun path => terminal (path (stoppingTime path + delay))) =ᵐ[
                      (globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))]
                  (fun path => semigroup delay terminal (path (stoppingTime path)))

theorem xiFiniteStoppingContinuousPathProperties_of_deterministicFamily (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate normalization : ℝ) (normalizationPositive : 0 < normalization)
    (familyProperties : XiDeterministicMarkovContinuousPathProperties system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive) :
    XiFiniteStoppingContinuousPathProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI xiFiniteStoppingProofLimitCompactSpace : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI xiFiniteStoppingProofLimitMeasurableSpace : MeasurableSpace parameters.LimitSpace := borel _
  letI xiFiniteStoppingProofLimitBorelSpace : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI xiFiniteStoppingProofPathMeasurableSpace : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI xiFiniteStoppingProofPathBorelSpace : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  dsimp only [XiDeterministicMarkovContinuousPathProperties, XiFiniteStoppingContinuousPathProperties]
    at familyProperties ⊢
  obtain ⟨semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    supLimit, positive, preservesOne, globalLaws, familyMeasurable, probabilityFamilyMeasurable,
    probabilityKernel, startingData⟩ := familyProperties
  refine ⟨semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    supLimit, positive, preservesOne, globalLaws, familyMeasurable, probabilityFamilyMeasurable,
    probabilityKernel, ?_⟩
  intro start
  obtain ⟨starts, startsConverge, laws, lawsConverge, lawsContinuous, lawsCompatible,
    initialDirac, finiteEvaluations, observations, deterministicIdentity⟩ := startingData start
  refine ⟨starts, startsConverge, laws, lawsConverge, lawsContinuous, lawsCompatible,
    initialDirac, finiteEvaluations, observations, deterministicIdentity, ?_⟩
  have banachObservations : ContinuousPathOrderedBanachObservations (globalLaws start) semigroup start := by
    intro times timesMonotone startsAtZero tests count terminal
    exact (observations times timesMonotone startsAtZero tests count terminal).trans
      (congrFun (ContinuousMarkov.kernelBackwardProduct_eq_semigroupBackwardProduct semigroup positive
        preservesOne _ terminal) start)
  intro stoppingTime stopping delay terminal
  refine ⟨?_, ?_⟩
  · intro event eventMeasurable
    exact continuousPath_finite_stoppingTime_setIntegral_markov (globalLaws start) semigroup start positive
      banachObservations stoppingTime stopping delay terminal event eventMeasurable
  · exact continuousPath_finite_stoppingTime_condExp_markov (globalLaws start) semigroup start positive
      banachObservations stoppingTime stopping delay terminal

theorem exists_xiFiniteStoppingContinuousPath_of_rules (system : EIGSData K)
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
      XiFiniteStoppingContinuousPathProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, familyProperties⟩ :=
    exists_xiDeterministicMarkovContinuousPath_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence,
    xiFiniteStoppingContinuousPathProperties_of_deterministicFamily system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive familyProperties⟩

end
end EIGS

#print axioms EIGS.xiFiniteStoppingContinuousPathProperties_of_deterministicFamily


#print axioms EIGS.exists_xiFiniteStoppingContinuousPath_of_rules

