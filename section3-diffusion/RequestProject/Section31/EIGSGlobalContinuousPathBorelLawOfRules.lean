import RequestProject.Section31.EIGSGlobalContinuousPathLawOfRules
import RequestProject.Section31.ContinuousTimePathBorel

/-! The actual global limit law is transported to the compact-open Borel
space of bundled continuous paths. Its finite observations are unchanged,
and its initial distribution is the prescribed Dirac mass. Discontinuous
finite-level step paths retain their original convergence carrier.
Measurability in the starting point and Hunt properties remain separate. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators
noncomputable section
set_option maxHeartbeats 4000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance actualGlobalBorelLawMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance actualGlobalBorelLawBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

theorem continuousTimePathLawToCompactOpen_ordered_integral
    (law : ProbabilityMeasure (ContinuousTimePath State)) (times : ℕ → ℝ≥0)
    (tests : ℕ → C(State, ℝ)) (count : ℕ) (terminal : C(State, ℝ)) :
    (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) *
      terminal (path (times count)) ∂(continuousTimePathLawToCompactOpen law : Measure C(ℝ≥0, State))) =
      ∫ path, (∏ index : Fin count, tests index.val (path.val (times index.val))) *
        terminal (path.val (times count)) ∂(law : Measure (ContinuousTimePath State)) := by
  let observation : C(ℝ≥0, State) → ℝ := fun path =>
    (∏ index : Fin count, tests index.val (path (times index.val))) * terminal (path (times count))
  have observationContinuous : Continuous observation :=
    (continuous_finset_prod Finset.univ fun index _ =>
      (tests index.val).continuous.comp (continuous_eval_const (times index.val))).mul
        (terminal.continuous.comp (continuous_eval_const (times count)))
  change (∫ path, observation path ∂(law : Measure (ContinuousTimePath State)).map
    (continuousTimePathMeasurableEquivContinuousMap (State := State))) = _
  rw [integral_map
    (continuousTimePathMeasurableEquivContinuousMap (State := State)).measurable.aemeasurable
    observationContinuous.measurable.aestronglyMeasurable]
  rfl

theorem continuousTimePathBorelLaw_initial_dirac
    (law : ProbabilityMeasure C(ℝ≥0, State)) (start : State)
    (initialIntegrals : ∀ function : C(State, ℝ),
      (∫ path, function (path 0) ∂(law : Measure C(ℝ≥0, State))) = function start) :
    (law : Measure C(ℝ≥0, State)).map (fun path => path 0) = Measure.dirac start := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro function
  rw [integral_map (continuous_eval_const (0 : ℝ≥0)).measurable.aemeasurable
    function.continuous.measurable.aestronglyMeasurable, integral_dirac]
  exact initialIntegrals function.toContinuousMap

theorem continuousTimePathBorelLaw_ae_initial
    (law : ProbabilityMeasure C(ℝ≥0, State)) (start : State)
    (initialDirac : (law : Measure C(ℝ≥0, State)).map (fun path => path 0) = Measure.dirac start) :
    ∀ᵐ path ∂(law : Measure C(ℝ≥0, State)), path 0 = start := by
  have projectedAE : ∀ᵐ point ∂(law : Measure C(ℝ≥0, State)).map
      (fun path => path 0), point = start := by
    rw [initialDirac]
    simp
  exact ae_of_ae_map (μ := (law : Measure C(ℝ≥0, State)))
    (f := fun path : C(ℝ≥0, State) => path 0) (p := fun point : State => point = start)
    (continuous_eval_const (0 : ℝ≥0)).measurable.aemeasurable projectedAE

end
end IGS.Sec31.DiscreteMarkov

namespace EIGS

open IGS.Sec31 MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical BigOperators NNReal UniformConvergence BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}
def XiGlobalContinuousPathBorelLawProperties (system : EIGSData K)
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
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
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
            ∃ globalLaw : ProbabilityMeasure C(ℝ≥0, parameters.LimitSpace),
              ((globalLaw : Measure C(ℝ≥0, parameters.LimitSpace)).map (fun path => path 0) = Measure.dirac start) ∧
              (∀ (horizon dimension : ℕ) (times : Fin dimension → ℝ≥0)
                (timesInHorizon : ∀ index, (times index : ℝ) ≤ horizon),
                (globalLaw : Measure C(ℝ≥0, parameters.LimitSpace)).map (fun path => fun index => path (times index)) =
                  (laws (horizon : ℝ≥0) : Measure (FiniteSupportPathSpace (paths (horizon : ℝ≥0)))).map (fun path => fun index => UniformFun.toFun path.val
                    ⟨(times index : ℝ), (times index).property, timesInHorizon index⟩)) ∧
              ∀ (times : ℕ → ℝ≥0) (timesMonotone : Monotone times), times 0 = 0 →
                ∀ (tests : ℕ → C(parameters.LimitSpace, ℝ)) (count : ℕ)
                  (terminal : C(parameters.LimitSpace, ℝ)),
                  (∫ path : C(ℝ≥0, parameters.LimitSpace), (∏ index : Fin count, tests index.val (path (times index.val))) *
                    terminal (path (times count)) ∂(globalLaw : Measure C(ℝ≥0, parameters.LimitSpace))) =
                    ContinuousMarkov.kernelBackwardProduct
                      (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
                      ((List.range count).map (fun index => (times (index + 1) - times index, tests index)))
                      terminal start
theorem xiGlobalContinuousPathBorelLawProperties_of_global (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate normalization : ℝ) (normalizationPositive : 0 < normalization)
    (globalProperties : XiGlobalContinuousPathLawProperties system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive) :
    XiGlobalContinuousPathBorelLawProperties system rulesConnected rulesLoopless rulesUnique
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
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  dsimp only [XiGlobalContinuousPathLawProperties, XiGlobalContinuousPathBorelLawProperties]
    at globalProperties ⊢
  obtain ⟨semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    supLimit, positive, preservesOne, globalLimits⟩ := globalProperties
  refine ⟨semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous,
    supLimit, positive, preservesOne, ?_⟩
  intro start
  obtain ⟨starts, startsConverge, laws, lawsConverge, lawsContinuous, lawsCompatible,
    rawLaw, finiteEvaluations, rawObservations⟩ := globalLimits start
  refine ⟨starts, startsConverge, laws, lawsConverge, lawsContinuous, lawsCompatible,
    continuousTimePathLawToCompactOpen rawLaw, ?_, ?_, ?_⟩
  · apply continuousTimePathBorelLaw_initial_dirac
    intro function
    have rawInitial : (∫ path : ContinuousTimePath parameters.LimitSpace, function (path.val 0) ∂(rawLaw : Measure (ContinuousTimePath parameters.LimitSpace))) = function start := by
      simpa [ContinuousMarkov.kernelBackwardProduct] using
        rawObservations (fun _ => 0) (fun _ _ _ => le_rfl) rfl (fun _ => 1) 0 function
    have transported :
        (∫ path, function (path 0)
          ∂(continuousTimePathLawToCompactOpen rawLaw : Measure C(ℝ≥0, parameters.LimitSpace))) =
        ∫ path : ContinuousTimePath parameters.LimitSpace, function (path.val 0) ∂(rawLaw : Measure (ContinuousTimePath parameters.LimitSpace)) := by
      simpa using continuousTimePathLawToCompactOpen_ordered_integral
        rawLaw (fun _ => 0) (fun _ => 1) 0 function
    exact transported.trans rawInitial
  · intro horizon dimension times timesInHorizon
    exact (continuousTimePathLawToCompactOpen_finite_evaluations rawLaw dimension times).trans
      (finiteEvaluations horizon dimension times timesInHorizon)
  · intro times timesMonotone startsAtZero tests count terminal
    exact (continuousTimePathLawToCompactOpen_ordered_integral rawLaw times tests count terminal).trans
      (rawObservations times timesMonotone startsAtZero tests count terminal)

theorem exists_xiGlobalContinuousPathBorelLaw_of_rules (system : EIGSData K)
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
      XiGlobalContinuousPathBorelLawProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, globalProperties⟩ :=
    exists_xiGlobalContinuousPathLaw_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence,
    xiGlobalContinuousPathBorelLawProperties_of_global system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive globalProperties⟩

end
end EIGS

#print axioms IGS.Sec31.DiscreteMarkov.continuousTimePathLawToCompactOpen_ordered_integral
#print axioms IGS.Sec31.DiscreteMarkov.continuousTimePathBorelLaw_initial_dirac
#print axioms IGS.Sec31.DiscreteMarkov.continuousTimePathBorelLaw_ae_initial
#print axioms EIGS.xiGlobalContinuousPathBorelLawProperties_of_global


#print axioms EIGS.exists_xiGlobalContinuousPathBorelLaw_of_rules



