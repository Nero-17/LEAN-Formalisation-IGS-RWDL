import RequestProject.Section31.EIGSSameNativeJointFullHeatPhysicalWeakLawOfRules
import RequestProject.Section31.EIGSExponentialSameRealisationTightness

/-! The same literal physical-clock full-heat/true-exit Hunt witness
receives unit and physical J1 uniform tightness in its existing GHPS
ambient. Every geometry and probability input is extracted internally. -/
namespace EIGS
open IGS.Sec31 MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical BigOperators NNReal UniformConvergence BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 12000000
variable {K : ℕ}
def XiOriginalMeasuredGHPSFullHeatExitPhysicalTightSemigroupProperties (system : EIGSData K)
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
  letI originalMeasuredGHPSDefinitionInstance01 : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI originalMeasuredGHPSDefinitionInstance02 : MeasurableSpace parameters.LimitSpace := borel _
  letI originalMeasuredGHPSDefinitionInstance03 : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI originalMeasuredGHPSDefinitionInstance04 : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI originalMeasuredGHPSDefinitionGlobalBorel : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  let rates := xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
    normalization normalizationPositive
  let paths := fun horizon => finiteHorizonStepPaths horizon rates parameters.vertexEmbedding
  letI originalMeasuredGHPSDefinitionStateBounded : BoundedSpace parameters.LimitSpace := ⟨Metric.isBounded_of_compactSpace⟩
  letI originalMeasuredGHPSDefinitionIntervalBounded : ∀ horizon : ℝ≥0,
      BoundedSpace (Set.Icc (0 : ℝ) (horizon : ℝ)) := fun _ => ⟨Metric.isBounded_of_compactSpace⟩
  letI originalMeasuredGHPSDefinitionPathMeasurable : ∀ horizon : ℝ≥0,
      MeasurableSpace (CadlagJ1Path (Set.Icc (0 : ℝ) (horizon : ℝ)) parameters.LimitSpace) := fun _ => borel _
  letI originalMeasuredGHPSDefinitionPathBorel : ∀ horizon : ℝ≥0,
      BorelSpace (CadlagJ1Path (Set.Icc (0 : ℝ) (horizon : ℝ)) parameters.LimitSpace) := fun _ => ⟨rfl⟩
  letI originalMeasuredGHPSDefinitionContinuousMapMeasurable : ∀ horizon : ℝ≥0,
      MeasurableSpace C(Set.Icc (0 : ℝ) (horizon : ℝ), parameters.LimitSpace) := fun _ => borel _
  letI originalMeasuredGHPSDefinitionContinuousMapBorel : ∀ horizon : ℝ≥0,
      BorelSpace C(Set.Icc (0 : ℝ) (horizon : ℝ), parameters.LimitSpace) := fun _ => ⟨rfl⟩
  fun (measure : Measure parameters.LimitSpace)
    (embedding : C(parameters.LimitSpace, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (closedSemigroup : ℝ≥0 → Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (exponent : ℝ)
    (semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ)) =>
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
          SameFamilyFullHeatKernelProperties measure embedding closedSemigroup exponent
            semigroup globalLaws familyMeasurable parameters.vertexEmbedding
            ((Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
              Real.log (mass.rate * resistanceRate))
            (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1)) ∧
          XiNativeContinuousBallSurvivalFamilyProperties system rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent distancePositive globalLaws ∧
          XiNormalizedContinuousBallSurvivalFamilyProperties system rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent distancePositive globalLaws ∧
          XiNativeContinuousBallMeanFamilyProperties system rulesConnected rulesLoopless rulesUnique
            distancePositive globalLaws ∧
          XiNormalizedContinuousBallMeanFamilyProperties system rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent distancePositive globalLaws ∧
          XiNativeExponentialGlobalWeakFamilyProperties system rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent distancePositive normalization normalizationPositive globalLaws ∧
          XiNativeExponentialPhysicalGlobalWeakFamilyProperties system rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent distancePositive normalization normalizationPositive globalLaws ∧
      ∃ (Ambient : Type) (ambientMetric : MetricSpace Ambient),
      letI originalMeasuredGHPSAmbientDefinitionMetric := ambientMetric
      ∃ ambientComplete : CompleteSpace Ambient,
      ∃ ambientCompact : CompactSpace Ambient,
      letI originalMeasuredGHPSAmbientDefinitionCompact := ambientCompact
      letI originalMeasuredGHPSAmbientDefinitionMeasurable : MeasurableSpace Ambient := borel _
      letI originalMeasuredGHPSAmbientDefinitionBorel : BorelSpace Ambient := ⟨rfl⟩
      letI originalMeasuredGHPSAmbientDefinitionBounded : BoundedSpace Ambient := ⟨Metric.isBounded_of_compactSpace⟩
      letI originalMeasuredGHPSAmbientDefinitionPathMeasurable : ∀ horizon : ℝ≥0,
          MeasurableSpace (CadlagJ1Path (Set.Icc (0 : ℝ) (horizon : ℝ)) Ambient) := fun _ => borel _
      letI originalMeasuredGHPSAmbientDefinitionPathBorel : ∀ horizon : ℝ≥0,
          BorelSpace (CadlagJ1Path (Set.Icc (0 : ℝ) (horizon : ℝ)) Ambient) := fun _ => ⟨rfl⟩
      ∃ target : parameters.LimitSpace → Ambient,
      ∃ targetContinuous : Continuous target,
        (letI originalMeasuredGHPSTargetDefinitionMetric : MetricSpace parameters.LimitSpace := MeasuredGHP.xiCompletionDiameterMetricSpace system rulesConnected
          parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
          distanceGreaterThanOne parameters.eigenpair
         Isometry target) ∧
      ∃ sources : ∀ level, XiVtx system level → Ambient,
        (∀ level, letI originalMeasuredGHPSSourceDefinitionMetric := MeasuredGHP.xiOriginalGraphDiameterMetricSpace system rulesConnected level
          Isometry (sources level)) ∧
      ∃ radii : ℕ → ℝ, (∀ level, 0 < radii level) ∧ Tendsto radii atTop (𝓝 0) ∧
        (∀ level vertex, dist (sources level vertex) (target (parameters.vertexEmbedding level vertex)) = radii level) ∧
      Tendsto (fun level => (MeasuredGHP.xiNativeVertexProbability system level).map
        (show Measurable (sources level) from Measurable.of_discrete).aemeasurable)
        atTop (𝓝 ((xiLimitProbabilityMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).map
            targetContinuous.measurable.aemeasurable)) ∧
      Tendsto (fun level => (MeasuredGHP.xiNativeSpeedProbability system mass level).map
        (show Measurable (sources level) from Measurable.of_discrete).aemeasurable)
        atTop (𝓝 ((xiLimitProbabilityMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).map
            targetContinuous.measurable.aemeasurable)) ∧
      Tendsto (fun level => levyProkhorovDist
        ((MeasuredGHP.xiNativeVertexProbability system level).map
          (show Measurable (sources level) from Measurable.of_discrete).aemeasurable).toMeasure
        ((xiLimitProbabilityMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).map
            targetContinuous.measurable.aemeasurable).toMeasure) atTop (𝓝 0) ∧
      Tendsto (fun level => levyProkhorovDist
        ((MeasuredGHP.xiNativeSpeedProbability system mass level).map
          (show Measurable (sources level) from Measurable.of_discrete).aemeasurable).toMeasure
        ((xiLimitProbabilityMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).map
            targetContinuous.measurable.aemeasurable).toMeasure) atTop (𝓝 0) ∧
      Tendsto (fun level => Metric.hausdorffDist (Set.range (sources level)) (Set.range target))
        atTop (𝓝 0) ∧
      (∀ initial : ∀ level, ProbabilityMeasure (XiVtx system level),
        ∀ horizon : ℝ≥0, ∀ horizonPositive : 0 < horizon,
        IsTightMeasureSet (Set.range (fun level =>
          (IGS.Sec31.PoissonClock.finiteGraphExponentialJ1Law (XiSimpleGraph system level)
            (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected level vertex))
            (initial level) (sources level) ((rates level : ℝ) * horizon)
            (mul_pos (xiNativeFiniteJumpRateNNReal_positive system rulesConnected distancePositive normalization normalizationPositive level)
              (by exact_mod_cast horizonPositive)) : Measure (UnitCadlagJ1Path Ambient)))) ∧
        IsTightMeasureSet (Set.range (fun level =>
          (IGS.Sec31.PoissonClock.finiteGraphExponentialPhysicalJ1Law (XiSimpleGraph system level)
            (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected level vertex))
            (initial level) (sources level) (rates level : ℝ)
            (xiNativeFiniteJumpRateNNReal_positive system rulesConnected distancePositive normalization normalizationPositive level)
            horizon horizonPositive : Measure (CadlagJ1Path (Set.Icc (0 : ℝ) (horizon : ℝ)) Ambient))))) ∧
      (∀ start : parameters.LimitSpace, ∀ starts : ∀ level, XiVtx system level,
        Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start) →
        ∀ horizon : ℝ≥0, ∀ horizonPositive : 0 < horizon,
          Tendsto (fun level => IGS.Sec31.PoissonClock.finiteGraphExponentialJ1Law (XiSimpleGraph system level)
            (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected level vertex))
            (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level))
            (sources level) ((rates level : ℝ) * horizon)
            (mul_pos (xiNativeFiniteJumpRateNNReal_positive system rulesConnected distancePositive normalization normalizationPositive level)
              (by exact_mod_cast horizonPositive))) atTop
            (𝓝 (ProbabilityMeasure.map
              (ProbabilityMeasure.map (globalLaws start)
                (continuousPathToUnitCadlagJ1_continuous horizon).measurable.aemeasurable)
              (cadlagJ1SpatialMap_continuous target targetContinuous).measurable.aemeasurable))) ∧
      (∀ start : parameters.LimitSpace, ∀ starts : ∀ level, XiVtx system level,
        Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start) →
        ∀ horizon : ℝ≥0, ∀ horizonPositive : 0 < horizon,
          Tendsto (fun level => IGS.Sec31.PoissonClock.finiteGraphExponentialPhysicalJ1Law (XiSimpleGraph system level)
            (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected level vertex))
            (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level))
            (sources level) (rates level : ℝ)
            (xiNativeFiniteJumpRateNNReal_positive system rulesConnected distancePositive normalization normalizationPositive level)
            horizon horizonPositive) atTop
            (𝓝 (ProbabilityMeasure.map
              (ProbabilityMeasure.map
                (ProbabilityMeasure.map (globalLaws start)
                  (continuousPathFiniteHorizonRestriction_continuous horizon).measurable.aemeasurable)
                compactContinuousMapToCadlagJ1_lipschitz.continuous.measurable.aemeasurable)
              (cadlagJ1SpatialMap_continuous target targetContinuous).measurable.aemeasurable))) ∧
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
              (∀ starts : ∀ level, XiVtx system level,
                Tendsto (fun level => sources level (starts level)) atTop (𝓝 (target start)) →
                ∀ horizon : ℝ≥0,
                  Tendsto (fun level =>
                    ProbabilityMeasure.map (⟨finiteHorizonPrefixLaw horizon rates
                      (fun level => xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
                      (fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level))) level,
                      inferInstance⟩ : ProbabilityMeasure
                        (Finset.Iic ⌊(horizon : ℝ) * (rates level : ℝ)⌋₊ → XiVtx system level))
                          (finiteHorizonHistoryCadlagJ1Map_measurable horizon rates sources level).aemeasurable)
                    atTop (𝓝 (cadlagJ1SpatialLaw target targetContinuous (((globalLaws start).map
                      (continuousPathFiniteHorizonRestriction_continuous horizon).measurable.aemeasurable).map
                        compactContinuousMapToCadlagJ1_lipschitz.continuous.measurable.aemeasurable)))) ∧
              ∀ (times : ℕ → ℝ≥0) (timesMonotone : Monotone times), times 0 = 0 →
                ∀ (tests : ℕ → C(parameters.LimitSpace, ℝ)) (count : ℕ)
                  (terminal : C(parameters.LimitSpace, ℝ)),
                  (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) *
                    terminal (path (times count)) ∂(globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))) =
                    ContinuousMarkov.kernelBackwardProduct
                      (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
                      ((List.range count).map (fun index => (times (index + 1) - times index, tests index)))
                      terminal start

def XiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalTightProperties (system : EIGSData K)
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
  letI originalMeasuredGHPSDefinitionInstance05 := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI originalMeasuredGHPSDefinitionInstance06 : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
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
      XiOriginalMeasuredGHPSFullHeatExitPhysicalTightSemigroupProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate normalization normalizationPositive
        (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
        (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
        (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense)
        (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) semigroup ∧
      (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
          (semigroup time function) =
        QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
          (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass function))

theorem xiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalTightProperties_of_physical
    (system : EIGSData K)
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
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (physicalProperties : XiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair normalization normalizationPositive) :
    XiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalTightProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair normalization normalizationPositive := by
  classical
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair
  letI : BoundedSpace parameters.LimitSpace := ⟨Metric.isBounded_of_compactSpace⟩
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  dsimp only [XiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalProperties] at physicalProperties
  obtain ⟨originalDense, semigroup, semigroupProperties, intertwining⟩ := physicalProperties
  dsimp only [XiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalTightProperties]
  refine ⟨originalDense, semigroup, ?_, intertwining⟩
  dsimp only [XiOriginalMeasuredGHPSFullHeatExitPhysicalSemigroupProperties] at semigroupProperties
  obtain ⟨semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, supLimit,
    positive, preservesOne, globalLaws, familyMeasurable, probabilityFamilyMeasurable,
    familyKernelMarkov, sameFamilyFullHeat, nativeSurvival, normalizedSurvival, nativeMean,
    normalizedMean, nativeUnitWeak, nativePhysicalWeak, ghpsProperties⟩ := semigroupProperties
  dsimp only [XiOriginalMeasuredGHPSFullHeatExitPhysicalTightSemigroupProperties]
  refine ⟨semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, supLimit,
    positive, preservesOne, globalLaws, familyMeasurable, probabilityFamilyMeasurable,
    familyKernelMarkov, sameFamilyFullHeat, nativeSurvival, normalizedSurvival, nativeMean,
    normalizedMean, nativeUnitWeak, nativePhysicalWeak, ?_⟩
  obtain ⟨Ambient, ambientMetric, ambientComplete, ambientCompact, target, targetContinuous,
    targetIsometry, sources, sourceIsometry, radii, radiiPositive, radiiZero, displacement,
    vertexConvergence, speedConvergence, vertexLP, speedLP, hausdorffConvergence,
    originalUnitWeak, originalPhysicalWeak, limits⟩ := ghpsProperties
  letI := ambientMetric
  letI := ambientCompact
  letI : BoundedSpace Ambient := ⟨Metric.isBounded_of_compactSpace⟩
  letI : MeasurableSpace Ambient := borel _
  letI : BorelSpace Ambient := ⟨rfl⟩
  refine ⟨Ambient, ambientMetric, ambientComplete, ambientCompact, target, targetContinuous,
    targetIsometry, sources, sourceIsometry, radii, radiiPositive, radiiZero, displacement,
    vertexConvergence, speedConvergence, vertexLP, speedLP, hausdorffConvergence,
    ?_, originalUnitWeak, originalPhysicalWeak, limits⟩
  exact xiExponentialJ1Laws_unit_and_physical_tight_in_same_realisation system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive normalization normalizationPositive
    Ambient target targetContinuous sources radii radiiZero (fun level vertex => (displacement level vertex).le)

end
end EIGS

#print axioms EIGS.xiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalTightProperties_of_physical

