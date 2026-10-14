import RequestProject.Section31.EIGSContinuousPathFamilyClosedIdentification
import RequestProject.Section31.EIGSFiniteHorizonMovingStartFullConvergenceOfRules
import Mathlib.MeasureTheory.Constructions.Projective

/-! The same closed-semigroup/global-path-law witness works for every
convergent moving start. Full moving-start convergence itself gives uniqueness
by mixing two start sequences on even and odd levels. Finite observations and
projective uniqueness identify the entire function-valued horizon restriction.
The restriction equality below uses the evaluation sigma algebra on all
functions; the actual weak convergence retains its original uniform carrier.
No original-metric normalization or Skorokhod transport is claimed here. -/

namespace IGS.Sec31.DiscreteMarkov

open Set Filter Topology MeasureTheory
open scoped Classical NNReal UniformConvergence
noncomputable section
set_option maxHeartbeats 6000000

theorem movingStart_limit_eq_of_all_sequences
    {State Outcome : Type*} [MetricSpace State] [TopologicalSpace Outcome] [T2Space Outcome]
    {Vertex : ℕ → Type*} (embedding : (level : ℕ) → Vertex level → State)
    (laws : (∀ level, Vertex level) → ℕ → Outcome)
    (locality : ∀ firstStarts secondStarts level,
      firstStarts level = secondStarts level → laws firstStarts level = laws secondStarts level)
    (start : State)
    (allSequences : ∀ starts : ∀ level, Vertex level,
      Tendsto (fun level => embedding level (starts level)) atTop (𝓝 start) →
        ∃ limit, Tendsto (laws starts) atTop (𝓝 limit))
    (firstStarts secondStarts : ∀ level, Vertex level)
    (firstStartsConverge : Tendsto (fun level => embedding level (firstStarts level)) atTop (𝓝 start))
    (secondStartsConverge : Tendsto (fun level => embedding level (secondStarts level)) atTop (𝓝 start))
    (firstLimit secondLimit : Outcome)
    (firstConverges : Tendsto (laws firstStarts) atTop (𝓝 firstLimit))
    (secondConverges : Tendsto (laws secondStarts) atTop (𝓝 secondLimit)) :
    firstLimit = secondLimit := by
  let mixedStarts : ∀ level, Vertex level :=
    fun level => if level % 2 = 0 then firstStarts level else secondStarts level
  have mixedStartsConverge : Tendsto (fun level => embedding level (mixedStarts level))
      atTop (𝓝 start) := by
    apply Metric.tendsto_nhds.mpr
    intro tolerance tolerancePositive
    filter_upwards [(Metric.tendsto_nhds.mp firstStartsConverge) tolerance tolerancePositive,
      (Metric.tendsto_nhds.mp secondStartsConverge) tolerance tolerancePositive]
      with level firstBound secondBound
    by_cases even : level % 2 = 0
    · simpa only [mixedStarts, if_pos even] using firstBound
    · simpa only [mixedStarts, if_neg even] using secondBound
  obtain ⟨mixedLimit, mixedConverges⟩ := allSequences mixedStarts mixedStartsConverge
  have evenStrict : StrictMono (fun index : ℕ => 2 * index) := by
    intro first second ordered
    change 2 * first < 2 * second
    omega
  have oddStrict : StrictMono (fun index : ℕ => 2 * index + 1) := by
    intro first second ordered
    change 2 * first + 1 < 2 * second + 1
    omega
  have mixedEvenConverges : Tendsto (fun index => laws firstStarts (2 * index))
      atTop (𝓝 mixedLimit) := by
    apply (mixedConverges.comp evenStrict.tendsto_atTop).congr'
    exact Eventually.of_forall fun index => locality mixedStarts firstStarts (2 * index)
      (by simp [mixedStarts])
  have mixedOddConverges : Tendsto (fun index => laws secondStarts (2 * index + 1))
      atTop (𝓝 mixedLimit) := by
    apply (mixedConverges.comp oddStrict.tendsto_atTop).congr'
    exact Eventually.of_forall fun index => locality mixedStarts secondStarts (2 * index + 1)
      (by simp [mixedStarts, Nat.add_mod, Nat.mul_mod])
  exact (tendsto_nhds_unique (firstConverges.comp evenStrict.tendsto_atTop) mixedEvenConverges).trans
    (tendsto_nhds_unique (secondConverges.comp oddStrict.tendsto_atTop) mixedOddConverges).symm

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]
variable [∀ level, MeasurableSpace (Vertex level)]
variable [∀ level, MeasurableSingletonClass (Vertex level)]

local instance movingRestrictionContinuousPathMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance movingRestrictionContinuousPathBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

theorem compatibleFiniteHorizonLaw_eq_globalRestriction
    (rates : ℕ → ℝ≥0) (embedding : (level : ℕ) → Vertex level → State)
    (laws : (horizon : ℝ≥0) → ProbabilityMeasure
      (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding)))
    (compatible : ∀ (shortHorizon longHorizon : ℝ≥0) (ordered : shortHorizon ≤ longHorizon),
      (laws longHorizon).map (finiteHorizonPathRestriction_continuous shortHorizon longHorizon ordered
        rates embedding).measurable.aemeasurable = laws shortHorizon)
    (globalLaw : ProbabilityMeasure C(ℝ≥0, State))
    (finiteEvaluations : ∀ (horizon dimension : ℕ) (times : Fin dimension → ℝ≥0)
      (inHorizon : ∀ index, (times index : ℝ) ≤ horizon),
      (globalLaw : Measure C(ℝ≥0, State)).map (fun path => fun index => path (times index)) =
        (laws (horizon : ℝ≥0) : Measure
          (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding))).map
          (fun path => fun index => UniformFun.toFun path.val
            ⟨(times index : ℝ), (times index).property, inHorizon index⟩))
    (horizon : ℝ≥0) :
    (laws horizon : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding))).map
      (fun path => UniformFun.toFun path.val) =
        (globalLaw : Measure C(ℝ≥0, State)).map
          (fun path => fun time : Icc (0 : ℝ) (horizon : ℝ) => path ⟨time.val, time.property.1⟩) := by
  have localEvaluationMeasurable : Measurable (fun path :
      FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding) =>
      UniformFun.toFun path.val) :=
    measurable_pi_lambda _ fun time =>
      (finiteSupportPathSpace_continuous_eval _ time).measurable
  have globalEvaluationMeasurable : Measurable (fun path : C(ℝ≥0, State) =>
      fun time : Icc (0 : ℝ) (horizon : ℝ) => path ⟨time.val, time.property.1⟩) :=
    measurable_pi_lambda _ fun time => (continuous_eval_const _).measurable
  let first := (laws horizon : Measure (FiniteSupportPathSpace
    (finiteHorizonStepPaths horizon rates embedding))).map (fun path => UniformFun.toFun path.val)
  let second := (globalLaw : Measure C(ℝ≥0, State)).map
    (fun path => fun time : Icc (0 : ℝ) (horizon : ℝ) => path ⟨time.val, time.property.1⟩)
  letI movingRestrictionFirstProbability : IsProbabilityMeasure first :=
    Measure.isProbabilityMeasure_map localEvaluationMeasurable.aemeasurable
  letI movingRestrictionSecondProbability : IsProbabilityMeasure second :=
    Measure.isProbabilityMeasure_map globalEvaluationMeasurable.aemeasurable
  change first = second
  apply IsProjectiveLimit.unique (P := fun indices => first.map indices.restrict)
  · intro indices
    rfl
  · intro indices
    let enumeration : indices ≃ Fin (Fintype.card indices) := Fintype.equivFin indices
    let times : Fin (Fintype.card indices) → ℝ≥0 := fun index =>
      ⟨(enumeration.symm index).val.val, (enumeration.symm index).val.property.1⟩
    let reorder : (Fin (Fintype.card indices) → State) → indices → State :=
      fun values index => values (enumeration index)
    have reorderMeasurable : Measurable reorder :=
      measurable_pi_lambda _ fun index => measurable_pi_apply (enumeration index)
    have restrictionMeasurable : Measurable
        (indices.restrict : (Icc (0 : ℝ) (horizon : ℝ) → State) → indices → State) :=
      measurable_pi_lambda _ fun index => measurable_pi_apply index.val
    have horizonOrdered : horizon ≤ (integerHorizonAbove horizon : ℝ≥0) := by
      exact_mod_cast time_le_integerHorizonAbove horizon
    have inIntegerHorizon (index : Fin (Fintype.card indices)) :
        (times index : ℝ) ≤ integerHorizonAbove horizon :=
      (enumeration.symm index).val.property.2.trans (time_le_integerHorizonAbove horizon)
    have projected := congrArg (Measure.map reorder)
      (finiteEvaluations (integerHorizonAbove horizon) (Fintype.card indices) times inIntegerHorizon)
    rw [Measure.map_map reorderMeasurable
        (measurable_pi_lambda _ fun index => (continuous_eval_const (times index)).measurable),
      Measure.map_map reorderMeasurable
        (measurable_pi_lambda _ fun index => (finiteSupportPathSpace_continuous_eval _ _).measurable)]
      at projected
    have compatibleMeasures : (laws (integerHorizonAbove horizon : ℝ≥0) : Measure
      (FiniteSupportPathSpace (finiteHorizonStepPaths (integerHorizonAbove horizon : ℝ≥0) rates embedding))).map
        (finiteHorizonPathRestriction horizon (integerHorizonAbove horizon : ℝ≥0) horizonOrdered rates embedding) =
          (laws horizon : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding))) := by
      simpa only [ProbabilityMeasure.toMeasure_map] using congrArg
        (fun law : ProbabilityMeasure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding)) =>
          law.toMeasure)
        (compatible horizon (integerHorizonAbove horizon : ℝ≥0) horizonOrdered)
    dsimp only [first, second]
    rw [Measure.map_map restrictionMeasurable globalEvaluationMeasurable,
      Measure.map_map restrictionMeasurable localEvaluationMeasurable, ← compatibleMeasures,
      Measure.map_map
        (restrictionMeasurable.comp localEvaluationMeasurable)
        (finiteHorizonPathRestriction_continuous horizon (integerHorizonAbove horizon : ℝ≥0)
          horizonOrdered rates embedding).measurable]
    convert projected using 1 <;> congr 1 <;> funext path index <;>
      simp only [reorder, times, Function.comp_apply, Equiv.symm_apply_apply] <;> rfl

end
end IGS.Sec31.DiscreteMarkov

namespace EIGS

open IGS.Sec31 MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical BigOperators NNReal UniformConvergence BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}

def XiAllMovingStartGlobalRestrictionSemigroupProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate normalization : ℝ) (normalizationPositive : 0 < normalization) :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI movingGlobalDefinitionInstance01 : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI movingGlobalDefinitionInstance02 : MeasurableSpace parameters.LimitSpace := borel _
  letI movingGlobalDefinitionInstance03 : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI movingGlobalDefinitionInstance04 : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
    normalization normalizationPositive
  let paths := fun horizon => finiteHorizonStepPaths horizon rates parameters.vertexEmbedding
  fun (semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ)) =>
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
        ∃ laws : (horizon : ℝ≥0) → ProbabilityMeasure (FiniteSupportPathSpace (paths horizon)),
            (∀ (starts : ∀ level, XiVtx system level),
              Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start) →
              ∀ horizon, Tendsto (fun level => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding
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
              (∀ horizon,
                (laws horizon : Measure (FiniteSupportPathSpace (paths horizon))).map
                  (fun path => UniformFun.toFun path.val) =
                    (globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace)).map
                      (fun path => fun time : Set.Icc (0 : ℝ) (horizon : ℝ) =>
                        path ⟨time.val, time.property.1⟩)) ∧
              ∀ (times : ℕ → ℝ≥0) (timesMonotone : Monotone times), times 0 = 0 →
                ∀ (tests : ℕ → C(parameters.LimitSpace, ℝ)) (count : ℕ)
                  (terminal : C(parameters.LimitSpace, ℝ)),
                  (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) *
                    terminal (path (times count)) ∂(globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))) =
                    ContinuousMarkov.kernelBackwardProduct
                      (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
                      ((List.range count).map (fun index => (times (index + 1) - times index, tests index)))
                      terminal start

def XiIdentifiedAllMovingStartGlobalRestrictionProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI movingGlobalDefinitionInstance05 := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI movingGlobalDefinitionInstance06 : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
    ∃ semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ),
      XiAllMovingStartGlobalRestrictionSemigroupProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate normalization normalizationPositive semigroup ∧
      (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
          (semigroup time function) =
        QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
          (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass function))

theorem xiAllMovingStartGlobalRestrictionSemigroupProperties_of_family (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate normalization : ℝ) (normalizationPositive : 0 < normalization)
    (semigroup : ℝ≥0 → C((xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique
      distancePositive).LimitSpace, ℝ) →L[ℝ]
        C((xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive).LimitSpace, ℝ))
    (familyProperties : XiMeasurableContinuousPathFamilySemigroupProperties system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive semigroup)
    (fullProperties : XiFiniteHorizonMovingStartFullConvergenceProperties system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive normalization normalizationPositive) :
    XiAllMovingStartGlobalRestrictionSemigroupProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive semigroup := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI movingGlobalStrengthenCompactSpace : CompactSpace parameters.LimitSpace :=
    xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI movingGlobalStrengthenMeasurableSpace : MeasurableSpace parameters.LimitSpace := borel _
  letI movingGlobalStrengthenBorelSpace : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI movingGlobalStrengthenPathMeasurableSpace : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI movingGlobalStrengthenPathBorelSpace : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive
  let kernels := fun level =>
    xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level
  dsimp only [XiMeasurableContinuousPathFamilySemigroupProperties,
    XiAllMovingStartGlobalRestrictionSemigroupProperties] at familyProperties ⊢
  obtain ⟨semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, supLimit, positive, preservesOne,
    globalLaws, familyMeasurable, probabilityFamilyMeasurable, familyKernelMarkov, globalLimits⟩ := familyProperties
  refine ⟨semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, supLimit, positive, preservesOne,
    globalLaws, familyMeasurable, probabilityFamilyMeasurable, familyKernelMarkov, ?_⟩
  intro start
  obtain ⟨selectedStarts, selectedStartsConverge, laws, selectedLawsConverge, lawsContinuous,
    lawsCompatible, initialDirac, finiteEvaluations, observations⟩ := globalLimits start
  refine ⟨laws, ?_, lawsContinuous, lawsCompatible, initialDirac, finiteEvaluations, ?_, observations⟩
  · intro starts startsConverge horizon
    dsimp only [XiFiniteHorizonMovingStartFullConvergenceProperties] at fullProperties
    obtain ⟨limit, limitConvergence, limitContinuous⟩ := fullProperties horizon starts start startsConverge
    have limitEquality : limit = laws horizon := by
      apply movingStart_limit_eq_of_all_sequences parameters.vertexEmbedding
        (fun chosenStarts => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding kernels
          (fun level => (⟨Measure.dirac (chosenStarts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level))))
        ?_ start ?_ starts selectedStarts startsConverge selectedStartsConverge
        limit (laws horizon) limitConvergence (selectedLawsConverge horizon)
      · intro firstStarts secondStarts level sameStart
        apply ProbabilityMeasure.toMeasure_injective
        rw [finiteHorizonStepLaw_eq_map, finiteHorizonStepLaw_eq_map]
        change (pathLaw (kernels level) (Measure.dirac (firstStarts level))).map
          (finiteHorizonStepMap horizon rates parameters.vertexEmbedding level) =
            (pathLaw (kernels level) (Measure.dirac (secondStarts level))).map
              (finiteHorizonStepMap horizon rates parameters.vertexEmbedding level)
        rw [sameStart]
      · intro otherStarts otherStartsConverge
        obtain ⟨otherLimit, otherConverges, _⟩ := fullProperties horizon otherStarts start otherStartsConverge
        exact ⟨otherLimit, otherConverges⟩
    rw [limitEquality] at limitConvergence
    exact limitConvergence
  · intro horizon
    exact compatibleFiniteHorizonLaw_eq_globalRestriction rates parameters.vertexEmbedding laws
      lawsCompatible (globalLaws start) finiteEvaluations horizon

theorem xiIdentifiedAllMovingStartGlobalRestrictionProperties_of_discrete (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (discreteProperties : XiNativeSupDiscreteConvergenceProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair normalization normalizationPositive) :
    XiIdentifiedAllMovingStartGlobalRestrictionProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI movingGlobalActualInstance01 := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI movingGlobalActualInstance02 : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  have identifiedProperties := xiIdentifiedMeasurableContinuousPathFamilyProperties_of_discrete system
    rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive discreteProperties
  have movingProperties := xiNativeSupMovingStartProductProperties_of_discreteConvergence system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive discreteProperties
  have arbitraryProperties := xiNativeSupArbitraryProductProperties_of_movingStartProducts system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair normalization normalizationPositive movingProperties
  have fullProperties := xiFiniteHorizonMovingStartFullConvergenceProperties_of_arbitraryProducts system
    rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive arbitraryProperties
  dsimp only [XiIdentifiedMeasurableContinuousPathFamilyProperties,
    XiIdentifiedAllMovingStartGlobalRestrictionProperties] at identifiedProperties ⊢
  obtain ⟨originalDense, semigroup, familyProperties, semigroupIntertwining⟩ := identifiedProperties
  refine ⟨originalDense, semigroup, ?_, semigroupIntertwining⟩
  exact xiAllMovingStartGlobalRestrictionSemigroupProperties_of_family system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive
    semigroup familyProperties fullProperties

theorem exists_xiIdentifiedAllMovingStartGlobalRestriction_of_rules (system : EIGSData K)
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
      XiIdentifiedAllMovingStartGlobalRestrictionProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, discreteProperties⟩ :=
    exists_xiNativeSupDiscreteConvergence_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiIdentifiedAllMovingStartGlobalRestrictionProperties_of_discrete system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive discreteProperties


end
end EIGS

#print axioms IGS.Sec31.DiscreteMarkov.movingStart_limit_eq_of_all_sequences
#print axioms IGS.Sec31.DiscreteMarkov.compatibleFiniteHorizonLaw_eq_globalRestriction
#print axioms EIGS.xiIdentifiedAllMovingStartGlobalRestrictionProperties_of_discrete
#print axioms EIGS.exists_xiIdentifiedAllMovingStartGlobalRestriction_of_rules
