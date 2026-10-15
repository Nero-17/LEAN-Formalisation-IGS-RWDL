import RequestProject.Section31.EIGSSameNativeJointFullHeatPhysicalWeakLawOfRules
import RequestProject.Section31.EIGSTwoColourOriginalDegreeSameFamilyFullHeat
import RequestProject.Section31.EIGSTwoColourSameKernelBrownianFullHeatExit

/-! Actual two-colour rule driver for the global degree point-count correction.
The accepted full physical Hunt/GHPS/heat/exit witness is selected once;
its original closed semigroup, global laws, and kernel witness are retained.
The supplied-family obligation is filled from the accepted Figure 3 witness; no primitive-degree hypothesis is introduced. -/
namespace EIGS
open IGS.Sec31 MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical BigOperators NNReal UniformConvergence BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 12000000


def XiTwoColourOriginalDegreeCorrectedPhysicalSemigroupProperties 
    (rulesConnected : ∀ colour, (ruleSG twoColourSystem colour).Connected)
    (rulesLoopless : ∀ colour, (twoColourSystem.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (twoColourSystem.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG twoColourSystem colour).Adj
      (twoColourSystem.plantPlus colour) (twoColourSystem.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin 2,
      ¬ ((twoColourSystem.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (twoColourSystem.plantPlus ruleColour) (twoColourSystem.plantMinus ruleColour))
    (resistanceRate normalization : ℝ) (normalizationPositive : 0 < normalization) :=
  let parameters := xiPathMetricDataOfRules twoColourSystem rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < twoColourSystem.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (twoColourSystem.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI originalMeasuredGHPSDefinitionInstance01 : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace twoColourSystem rulesConnected
    parameters.lengths parameters.lengthsPositive (twoColourSystem.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI originalMeasuredGHPSDefinitionInstance02 : MeasurableSpace parameters.LimitSpace := borel _
  letI originalMeasuredGHPSDefinitionInstance03 : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI originalMeasuredGHPSDefinitionInstance04 : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI originalMeasuredGHPSDefinitionGlobalBorel : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  let mass := xiMassParametersOfRules twoColourSystem rulesConnected distancePositive
  let rates := xiNativeFiniteJumpRateNNReal twoColourSystem rulesConnected distancePositive
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
      Tendsto (fun level => ‖xiNativeSupSemigroup twoColourSystem rulesConnected level resistanceRate normalization time
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
            ((Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix twoColourSystem))) /
              Real.log (mass.rate * resistanceRate))
            (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix twoColourSystem)) - 1)) ∧
          (twoColourOriginalDegreeDimension = Real.log (3 + Real.sqrt 6) / Real.log 2 ∧
    0 < twoColourOriginalDegreeDimension ∧
    Tendsto (fun value : ℝ => Real.log (twoColourDegreeMultiplicity value : ℝ) / (-Real.log value))
      (𝓝[twoColourOccupiedDegreeSupport] (0 : ℝ)) (𝓝 twoColourOriginalDegreeDimension) ∧
    NeBot (𝓝[twoColourOccupiedDegreeSupport] (0 : ℝ)) ∧
    SameFamilyFullHeatKernelProperties measure embedding closedSemigroup
      (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) semigroup globalLaws familyMeasurable parameters.vertexEmbedding
      ((Real.log mass.rate / Real.log (mass.rate * resistanceRate)) *
        (1 - 1 / twoColourOriginalDegreeDimension))
      (1 / (twoColourOriginalDegreeDimension - 1))) ∧
          XiNativeContinuousBallSurvivalFamilyProperties twoColourSystem rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent distancePositive globalLaws ∧
          XiNormalizedContinuousBallSurvivalFamilyProperties twoColourSystem rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent distancePositive globalLaws ∧
          XiNativeContinuousBallMeanFamilyProperties twoColourSystem rulesConnected rulesLoopless rulesUnique
            distancePositive globalLaws ∧
          XiNormalizedContinuousBallMeanFamilyProperties twoColourSystem rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent distancePositive globalLaws ∧
          XiNativeExponentialGlobalWeakFamilyProperties twoColourSystem rulesConnected rulesLoopless rulesUnique
            plantingNonadjacent distancePositive normalization normalizationPositive globalLaws ∧
          XiNativeExponentialPhysicalGlobalWeakFamilyProperties twoColourSystem rulesConnected rulesLoopless rulesUnique
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
        (letI originalMeasuredGHPSTargetDefinitionMetric : MetricSpace parameters.LimitSpace := MeasuredGHP.xiCompletionDiameterMetricSpace twoColourSystem rulesConnected
          parameters.lengths parameters.lengthsPositive (twoColourSystem.distanceSpectralRadius rulesConnected)
          distanceGreaterThanOne parameters.eigenpair
         Isometry target) ∧
      ∃ sources : ∀ level, XiVtx twoColourSystem level → Ambient,
        (∀ level, letI originalMeasuredGHPSSourceDefinitionMetric := MeasuredGHP.xiOriginalGraphDiameterMetricSpace twoColourSystem rulesConnected level
          Isometry (sources level)) ∧
      ∃ radii : ℕ → ℝ, (∀ level, 0 < radii level) ∧ Tendsto radii atTop (𝓝 0) ∧
        (∀ level vertex, dist (sources level vertex) (target (parameters.vertexEmbedding level vertex)) = radii level) ∧
      Tendsto (fun level => (MeasuredGHP.xiNativeVertexProbability twoColourSystem level).map
        (show Measurable (sources level) from Measurable.of_discrete).aemeasurable)
        atTop (𝓝 ((xiLimitProbabilityMeasure twoColourSystem rulesConnected parameters.lengths parameters.lengthsPositive
          (twoColourSystem.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).map
            targetContinuous.measurable.aemeasurable)) ∧
      Tendsto (fun level => (MeasuredGHP.xiNativeSpeedProbability twoColourSystem mass level).map
        (show Measurable (sources level) from Measurable.of_discrete).aemeasurable)
        atTop (𝓝 ((xiLimitProbabilityMeasure twoColourSystem rulesConnected parameters.lengths parameters.lengthsPositive
          (twoColourSystem.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).map
            targetContinuous.measurable.aemeasurable)) ∧
      Tendsto (fun level => levyProkhorovDist
        ((MeasuredGHP.xiNativeVertexProbability twoColourSystem level).map
          (show Measurable (sources level) from Measurable.of_discrete).aemeasurable).toMeasure
        ((xiLimitProbabilityMeasure twoColourSystem rulesConnected parameters.lengths parameters.lengthsPositive
          (twoColourSystem.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).map
            targetContinuous.measurable.aemeasurable).toMeasure) atTop (𝓝 0) ∧
      Tendsto (fun level => levyProkhorovDist
        ((MeasuredGHP.xiNativeSpeedProbability twoColourSystem mass level).map
          (show Measurable (sources level) from Measurable.of_discrete).aemeasurable).toMeasure
        ((xiLimitProbabilityMeasure twoColourSystem rulesConnected parameters.lengths parameters.lengthsPositive
          (twoColourSystem.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).map
            targetContinuous.measurable.aemeasurable).toMeasure) atTop (𝓝 0) ∧
      Tendsto (fun level => Metric.hausdorffDist (Set.range (sources level)) (Set.range target))
        atTop (𝓝 0) ∧
      (∀ start : parameters.LimitSpace, ∀ starts : ∀ level, XiVtx twoColourSystem level,
        Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start) →
        ∀ horizon : ℝ≥0, ∀ horizonPositive : 0 < horizon,
          Tendsto (fun level => IGS.Sec31.PoissonClock.finiteGraphExponentialJ1Law (XiSimpleGraph twoColourSystem level)
            (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive twoColourSystem rulesConnected level vertex))
            (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx twoColourSystem level))
            (sources level) ((rates level : ℝ) * horizon)
            (mul_pos (xiNativeFiniteJumpRateNNReal_positive twoColourSystem rulesConnected distancePositive normalization normalizationPositive level)
              (by exact_mod_cast horizonPositive))) atTop
            (𝓝 (ProbabilityMeasure.map
              (ProbabilityMeasure.map (globalLaws start)
                (continuousPathToUnitCadlagJ1_continuous horizon).measurable.aemeasurable)
              (cadlagJ1SpatialMap_continuous target targetContinuous).measurable.aemeasurable))) ∧
      (∀ start : parameters.LimitSpace, ∀ starts : ∀ level, XiVtx twoColourSystem level,
        Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start) →
        ∀ horizon : ℝ≥0, ∀ horizonPositive : 0 < horizon,
          Tendsto (fun level => IGS.Sec31.PoissonClock.finiteGraphExponentialPhysicalJ1Law (XiSimpleGraph twoColourSystem level)
            (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive twoColourSystem rulesConnected level vertex))
            (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx twoColourSystem level))
            (sources level) (rates level : ℝ)
            (xiNativeFiniteJumpRateNNReal_positive twoColourSystem rulesConnected distancePositive normalization normalizationPositive level)
            horizon horizonPositive) atTop
            (𝓝 (ProbabilityMeasure.map
              (ProbabilityMeasure.map
                (ProbabilityMeasure.map (globalLaws start)
                  (continuousPathFiniteHorizonRestriction_continuous horizon).measurable.aemeasurable)
                compactContinuousMapToCadlagJ1_lipschitz.continuous.measurable.aemeasurable)
              (cadlagJ1SpatialMap_continuous target targetContinuous).measurable.aemeasurable))) ∧
      ∀ start : parameters.LimitSpace,
        ∃ laws : (horizon : ℝ≥0) → ProbabilityMeasure (FiniteSupportPathSpace (paths horizon)),
            (∀ (starts : ∀ level, XiVtx twoColourSystem level),
              Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start) →
              ∀ horizon, Tendsto (fun level => finiteHorizonStepLaw horizon rates parameters.vertexEmbedding
                (fun level => xiNativeDiscreteKernel twoColourSystem rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
                (fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx twoColourSystem level))) level)
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
              (∀ starts : ∀ level, XiVtx twoColourSystem level,
                Tendsto (fun level => sources level (starts level)) atTop (𝓝 (target start)) →
                ∀ horizon : ℝ≥0,
                  Tendsto (fun level =>
                    ProbabilityMeasure.map (⟨finiteHorizonPrefixLaw horizon rates
                      (fun level => xiNativeDiscreteKernel twoColourSystem rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
                      (fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx twoColourSystem level))) level,
                      inferInstance⟩ : ProbabilityMeasure
                        (Finset.Iic ⌊(horizon : ℝ) * (rates level : ℝ)⌋₊ → XiVtx twoColourSystem level))
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

def XiIdentifiedTwoColourOriginalDegreeCorrectedPhysicalProperties 
    (rulesConnected : ∀ colour, (ruleSG twoColourSystem colour).Connected)
    (rulesLoopless : ∀ colour, (twoColourSystem.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (twoColourSystem.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG twoColourSystem colour).Adj
      (twoColourSystem.plantPlus colour) (twoColourSystem.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin 2,
      ¬ ((twoColourSystem.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (twoColourSystem.plantPlus ruleColour) (twoColourSystem.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin 2 → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (twoColourSystem.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
  let parameters := xiPathMetricDataOfRules twoColourSystem rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < twoColourSystem.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (twoColourSystem.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules twoColourSystem rulesConnected distancePositive
  letI originalMeasuredGHPSDefinitionInstance05 := xiCompletion_compactSpace twoColourSystem rulesConnected
    parameters.lengths parameters.lengthsPositive (twoColourSystem.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI originalMeasuredGHPSDefinitionInstance06 : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace twoColourSystem rulesConnected
    parameters.lengths parameters.lengthsPositive (twoColourSystem.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core twoColourSystem rulesConnected parameters.lengths parameters.lengthsPositive
    (twoColourSystem.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain twoColourSystem rulesConnected parameters.lengths parameters.lengthsPositive
    (twoColourSystem.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm twoColourSystem rulesConnected parameters.lengths parameters.lengthsPositive
    (twoColourSystem.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative twoColourSystem rulesConnected parameters.lengths parameters.lengthsPositive
    (twoColourSystem.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let oneColourDistance : (2 : ℕ) = 1 → ∀ colour,
      2 ≤ (ruleSG twoColourSystem colour).dist (twoColourSystem.plantPlus colour) (twoColourSystem.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (twoColourSystem.plant_ne colour) (plantingNonadjacent colour)
  let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive twoColourSystem rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (twoColourSystem.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure twoColourSystem rulesConnected
      parameters.lengths parameters.lengthsPositive (twoColourSystem.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
    ∃ semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ),
      XiTwoColourOriginalDegreeCorrectedPhysicalSemigroupProperties rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate normalization normalizationPositive
        (xiLimitMeasure twoColourSystem rulesConnected parameters.lengths parameters.lengthsPositive
          (twoColourSystem.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
        (xiContinuousL2Map twoColourSystem rulesConnected parameters.lengths parameters.lengthsPositive
          (twoColourSystem.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
        (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense)
        (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) semigroup ∧
      (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        xiContinuousL2Map twoColourSystem rulesConnected parameters.lengths parameters.lengthsPositive
          (twoColourSystem.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
          (semigroup time function) =
        QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
          (xiContinuousL2Map twoColourSystem rulesConnected parameters.lengths parameters.lengthsPositive
            (twoColourSystem.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass function))

theorem xiIdentifiedTwoColourOriginalDegreeCorrectedPhysicalProperties_of_physical
    
    (rulesConnected : ∀ colour, (ruleSG twoColourSystem colour).Connected)
    (rulesLoopless : ∀ colour, (twoColourSystem.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (twoColourSystem.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG twoColourSystem colour).Adj
      (twoColourSystem.plantPlus colour) (twoColourSystem.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin 2,
      ¬ ((twoColourSystem.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (twoColourSystem.plantPlus ruleColour) (twoColourSystem.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin 2 → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (twoColourSystem.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (physicalProperties : XiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalProperties twoColourSystem rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair normalization normalizationPositive) :
    XiIdentifiedTwoColourOriginalDegreeCorrectedPhysicalProperties rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair normalization normalizationPositive := by
  classical
  let parameters := xiPathMetricDataOfRules twoColourSystem rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < twoColourSystem.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (twoColourSystem.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace twoColourSystem rulesConnected
    parameters.lengths parameters.lengthsPositive (twoColourSystem.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair
  letI : BoundedSpace parameters.LimitSpace := ⟨Metric.isBounded_of_compactSpace⟩
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  dsimp only [XiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalProperties] at physicalProperties
  obtain ⟨originalDense, semigroup, semigroupProperties, intertwining⟩ := physicalProperties
  dsimp only [XiIdentifiedTwoColourOriginalDegreeCorrectedPhysicalProperties]
  refine ⟨originalDense, semigroup, ?_, intertwining⟩
  dsimp only [XiOriginalMeasuredGHPSFullHeatExitPhysicalSemigroupProperties] at semigroupProperties
  obtain ⟨semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, supLimit,
    positive, preservesOne, globalLaws, familyMeasurable, probabilityFamilyMeasurable,
    familyKernelMarkov, sameFamilyFullHeat, nativeSurvival, normalizedSurvival, nativeMean,
    normalizedMean, nativeUnitWeak, nativePhysicalWeak, ghpsProperties⟩ := semigroupProperties
  have originalDegreeCorrection := twoColourSystem_original_degree_same_family_full_heat
    (xiMassParametersOfRules twoColourSystem rulesConnected distancePositive) resistanceRate
    _ _ _ semigroup globalLaws familyMeasurable parameters.vertexEmbedding sameFamilyFullHeat
  dsimp only [XiTwoColourOriginalDegreeCorrectedPhysicalSemigroupProperties]
  exact ⟨semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, supLimit,
    positive, preservesOne, globalLaws, familyMeasurable, probabilityFamilyMeasurable,
    familyKernelMarkov, sameFamilyFullHeat, originalDegreeCorrection, nativeSurvival, normalizedSurvival,
    nativeMean, normalizedMean, nativeUnitWeak, nativePhysicalWeak, ghpsProperties⟩
theorem exists_twoColour_original_degree_corrected_same_kernel_Brownian_full_heat_physical :
    let parameters := xiPathMetricDataOfRules twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_distancePositive
    let distanceGreaterThanOne : 1 < twoColourSystem.distanceSpectralRadius twoColourSystem_connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (twoColourSystem.two_le_distanceSpectralRadius twoColourSystem_connected twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent twoColourSystem_distancePositive)
    let mass := xiMassParametersOfRules twoColourSystem twoColourSystem_connected twoColourSystem_distancePositive
    letI := xiCompletion_compactSpace twoColourSystem twoColourSystem_connected parameters.lengths parameters.lengthsPositive
      (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) distanceGreaterThanOne parameters.eigenpair
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
    ∃ resistanceVector : Fin 2 → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
    ∃ eigenpair : ∀ colour, (twoColourSystem.ruleFamily twoColourSystem_connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
    ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (twoColourSystem.ruleFamily twoColourSystem_connected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      1 < resistanceRate ∧
      resistanceRate = twoColourResistanceRate ∧
      ((1.1159 : ℝ) < 2 * (Real.log mass.rate - Real.log 2) / Real.log (mass.rate * resistanceRate) ∧
        2 * (Real.log mass.rate - Real.log 2) / Real.log (mass.rate * resistanceRate) < 1.1161) ∧
      ((1.8876 : ℝ) < 2 * Real.log mass.rate / Real.log (mass.rate * resistanceRate) ∧
        2 * Real.log mass.rate / Real.log (mass.rate * resistanceRate) < 1.8878) ∧
      Nonempty (XiContinuousResistanceFormRealization twoColourSystem twoColourSystem_connected parameters.lengths parameters.lengthsPositive
        (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) distanceGreaterThanOne parameters.eigenpair resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair (xiVertexEmbedding twoColourSystem 0 true)) ∧
      XiResistanceFormClosedIdentification twoColourSystem twoColourSystem_connected parameters.lengths parameters.lengthsPositive
        (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair ∧
      XiIdentifiedTwoColourOriginalDegreeCorrectedPhysicalProperties twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
        twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiIdentifiedOriginalMeasuredGHPSFullHeatExitProperties twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
        twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiIdentifiedOriginalMeasuredGHPSBrownianFullHeatProperties twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
        twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
        twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiSameKernelFullHeatEstimatesProperties twoColourSystem twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
        twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      (xiActualRecurrent twoColourSystem ↔ 2 * (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) < 2) := by
  intro parameters distanceGreaterThanOne mass
  letI := xiCompletion_compactSpace twoColourSystem twoColourSystem_connected parameters.lengths parameters.lengthsPositive
    (twoColourSystem.distanceSpectralRadius twoColourSystem_connected) distanceGreaterThanOne parameters.eigenpair
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, rateGreaterThanOne, rateEquality,
    finiteNumeric, typicalNumeric, realization, closedIdentification, exitProperties,
    brownianProperties, jointProperties, heatEstimates, recurrence⟩ :=
      exists_twoColour_same_kernel_Brownian_full_heat_exit
  have unitProperties := xiIdentifiedOriginalMeasuredGHPSFullHeatExitExponentialProperties_of_full_heat_exit twoColourSystem
    twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
    twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    normalization normalizationPositive exitProperties
  have physicalProperties := xiIdentifiedOriginalMeasuredGHPSFullHeatExitPhysicalProperties_of_unit twoColourSystem
    twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
    twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    normalization normalizationPositive unitProperties
  have correctedProperties := xiIdentifiedTwoColourOriginalDegreeCorrectedPhysicalProperties_of_physical
    twoColourSystem_connected twoColourSystem_loopless twoColourSystem_edgesUnique twoColourSystem_plantingNonadjacent
    twoColourSystem_distancePositive resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    normalization normalizationPositive physicalProperties
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, rateGreaterThanOne, rateEquality,
    finiteNumeric, typicalNumeric, realization, closedIdentification, correctedProperties,
    exitProperties, brownianProperties, jointProperties, heatEstimates, recurrence⟩

end
end EIGS

#print axioms EIGS.xiIdentifiedTwoColourOriginalDegreeCorrectedPhysicalProperties_of_physical
#print axioms EIGS.exists_twoColour_original_degree_corrected_same_kernel_Brownian_full_heat_physical

