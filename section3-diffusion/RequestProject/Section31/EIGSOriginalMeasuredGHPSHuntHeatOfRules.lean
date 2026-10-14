import RequestProject.Section31.EIGSOriginalMeasuredGHPSOfRules
import RequestProject.Section31.EIGSStrictPositiveJointContinuousHeatKernelDensityOfRules
import RequestProject.Section31.ContinuousPathSameFamilyClosedHeatKernel

/-! One native resistance and clock witness, one continuous semigroup and
one global family carry the closed-form identification, full conservative
Hunt criteria, strictly positive jointly continuous transition density,
and measured finite-horizon GHPS convergence. The actual closed-L2 embedding
is injective, so the internally constructed heat semigroup is identified
with this very process semigroup. No equality of independent existential
witnesses is assumed. Candidate only; compilation is still required. -/

namespace EIGS
open IGS.Sec31 MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical BigOperators NNReal UniformConvergence BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 9000000
variable {K : ℕ}
def XiOriginalMeasuredGHPSHuntHeatSemigroupProperties (system : EIGSData K)
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
          ContinuousPathSameFamilyClosedHeatKernelProperties measure embedding closedSemigroup exponent
            semigroup globalLaws familyMeasurable ∧
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
        (letI originalMeasuredGHPSTargetDefinitionMetric := MeasuredGHP.xiCompletionDiameterMetricSpace system rulesConnected
          parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
          distanceGreaterThanOne parameters.eigenpair
         Isometry target) ∧
      ∃ sources : ∀ level, XiVtx system level → Ambient,
        (∀ level, letI originalMeasuredGHPSSourceDefinitionMetric := MeasuredGHP.xiOriginalGraphDiameterMetricSpace system rulesConnected level
          Isometry (sources level)) ∧
      ∃ radii : ℕ → ℝ, (∀ level, 0 < radii level) ∧ Tendsto radii atTop (𝓝 0) ∧
        (∀ level vertex, dist (sources level vertex) (target (parameters.vertexEmbedding level vertex)) = radii level) ∧
      Tendsto (fun level => (xiNativeVertexProbability system level).map
        (show Measurable (sources level) from Measurable.of_discrete).aemeasurable)
        atTop (𝓝 ((xiLimitProbabilityMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).map
            targetContinuous.measurable.aemeasurable)) ∧
      Tendsto (fun level => (xiNativeSpeedProbability system mass level).map
        (show Measurable (sources level) from Measurable.of_discrete).aemeasurable)
        atTop (𝓝 ((xiLimitProbabilityMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).map
            targetContinuous.measurable.aemeasurable)) ∧
      Tendsto (fun level => levyProkhorovDist
        ((xiNativeVertexProbability system level).map
          (show Measurable (sources level) from Measurable.of_discrete).aemeasurable).toMeasure
        ((xiLimitProbabilityMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).map
            targetContinuous.measurable.aemeasurable).toMeasure) atTop (𝓝 0) ∧
      Tendsto (fun level => levyProkhorovDist
        ((xiNativeSpeedProbability system mass level).map
          (show Measurable (sources level) from Measurable.of_discrete).aemeasurable).toMeasure
        ((xiLimitProbabilityMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).map
            targetContinuous.measurable.aemeasurable).toMeasure) atTop (𝓝 0) ∧
      Tendsto (fun level => Metric.hausdorffDist (Set.range (sources level)) (Set.range target))
        atTop (𝓝 0) ∧
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

def XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties (system : EIGSData K)
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
      XiOriginalMeasuredGHPSHuntHeatSemigroupProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
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


theorem xiIdentifiedOriginalMeasuredGHPSHuntHeatProperties_of_measured (system : EIGSData K)
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
    (properties : XiIdentifiedOriginalMeasuredGHPSProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive) :
    XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
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
  letI sameWitnessLimitMeasurable : MeasurableSpace parameters.LimitSpace := borel _
  letI sameWitnessLimitBorel : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI sameWitnessGlobalMeasurable : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI sameWitnessGlobalBorel : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  dsimp only [XiIdentifiedOriginalMeasuredGHPSProperties,
    XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties] at properties ⊢
  obtain ⟨originalDense, semigroup, semigroupProperties, intertwining⟩ := properties
  have baseProperties := semigroupProperties
  dsimp only [XiOriginalMeasuredGHPSSemigroupProperties,
    XiOriginalMeasuredGHPSHuntHeatSemigroupProperties] at baseProperties
  obtain ⟨semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, supLimit,
    positive, preservesOne, globalLaws, familyMeasurable, probabilityFamilyMeasurable,
    familyKernelMarkov, Ambient, ambientMetric, ambientComplete, ambientCompact,
    target, targetContinuous, targetIsometry, sources, sourceIsometry,
    radii, radiiPositive, radiiZero, displacement, vertexConvergence, speedConvergence,
    vertexLP, speedLP, hausdorffConvergence, limits⟩ := baseProperties
  have continuousProperties : XiContinuousSemigroupProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair := by
    dsimp only [XiContinuousSemigroupProperties]
    exact ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd,
      semigroupContinuous, intertwining⟩
  have smoothing := xiContinuousSemigroupSmoothingProperties_of_continuousSemigroup system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair continuousProperties
  have compactSmoothing := xiContinuousSemigroupCompactSmoothingProperties_of_smoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair smoothing
  have allTimeCompact := xiContinuousAllTimeCompactSmoothingProperties_of_compactSmoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair compactSmoothing
  have heat := xiJointContinuousHeatKernelDensityProperties_of_compactSmoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair allTimeCompact
  have strictHeat := xiStrictPositiveJointContinuousHeatKernelDensityProperties_of_density system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair heat
  dsimp only [XiStrictPositiveJointContinuousHeatKernelDensityProperties] at strictHeat
  obtain ⟨heatDense, heatSemigroup, _, _, _, _, heatIntertwining,
    timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive,
    kernel, jointContinuous, density⟩ := strictHeat
  have denseEquality : heatDense = originalDense := Subsingleton.elim _ _
  subst heatDense
  have semigroupEquality : heatSemigroup = semigroup := by
    funext time
    apply ContinuousLinearMap.ext
    intro function
    apply xiContinuousL2Map_injective system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    exact (heatIntertwining time function).trans (intertwining time function).symm
  subst heatSemigroup
  have normal : ∀ start,
      (globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace)).map (fun path => path 0) =
        Measure.dirac start := by
    intro start
    obtain ⟨laws, _, _, _, initialDirac, _, _, _, _⟩ := limits start
    exact initialDirac
  have orderedObservations : ∀ (start : parameters.LimitSpace) (times : ℕ → ℝ≥0),
      Monotone times → times 0 = 0 →
      ∀ (tests : ℕ → C(parameters.LimitSpace, ℝ)) (count : ℕ)
        (terminal : C(parameters.LimitSpace, ℝ)),
      (∫ path, (∏ index : Fin count, tests index.val (path (times index.val))) *
        terminal (path (times count)) ∂(globalLaws start : Measure C(ℝ≥0, parameters.LimitSpace))) =
        ContinuousMarkov.kernelBackwardProduct
          (ContinuousMarkov.semigroupKernel semigroup positive preservesOne)
          ((List.range count).map (fun index => (times (index + 1) - times index, tests index))) terminal start := by
    intro start
    obtain ⟨laws, _, _, _, _, _, _, _, observations⟩ := limits start
    exact observations
  have familyHeat := continuousPath_sameFamilyClosedHeatKernelProperties_of_kernel
    (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
    (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
    (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense)
    (Real.log mass.rate / Real.log (mass.rate * resistanceRate))
    semigroup positive preservesOne globalLaws familyMeasurable probabilityFamilyMeasurable
    normal orderedObservations timeThreshold timeThresholdPositive upperConstant upperConstantPositive
    kernel jointContinuous density
  refine ⟨originalDense, semigroup, ?_, intertwining⟩
  dsimp only [XiOriginalMeasuredGHPSHuntHeatSemigroupProperties]
  exact ⟨semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, supLimit,
    positive, preservesOne, globalLaws, familyMeasurable, probabilityFamilyMeasurable,
    familyKernelMarkov, familyHeat, Ambient, ambientMetric, ambientComplete, ambientCompact,
    target, targetContinuous, targetIsometry, sources, sourceIsometry,
    radii, radiiPositive, radiiZero, displacement, vertexConvergence, speedConvergence,
    vertexLP, speedLP, hausdorffConvergence, limits⟩
theorem exists_xiIdentifiedOriginalMeasuredGHPSHuntHeat_of_rules (system : EIGSData K)
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
      XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, properties⟩ :=
    exists_xiIdentifiedOriginalMeasuredGHPS_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence,
    xiIdentifiedOriginalMeasuredGHPSHuntHeatProperties_of_measured system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive properties⟩

theorem exists_xiIdentifiedOriginalMeasuredGHPSHuntHeatPaperClock_of_rules (system : EIGSData K)
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
        Tendsto (fun level => fun colour =>
          (system.ruleFamily rulesConnected).Psi^[level] (fun _ => 1) colour / resistanceRate ^ level)
          atTop (𝓝 (normalization • resistanceVector)) ∧
        XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
          normalization normalizationPositive ∧
        (∀ level, (xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive level : ℝ) =
          xiPaperFiniteWalkClock system level resistanceRate normalization) ∧
        ∀ level (time : ℝ),
          ⌊time * (xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive level : ℝ)⌋₊ =
            ⌊time * xiPaperFiniteWalkClock system level resistanceRate normalization⌋₊ := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, pathProperties⟩ :=
    exists_xiIdentifiedOriginalMeasuredGHPSHuntHeat_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, pathProperties,
    xiNativeFiniteJumpRateNNReal_eq_paperClock system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive,
    xiNative_floor_index_eq_paperClock system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive⟩
end
end EIGS

#print axioms EIGS.xiIdentifiedOriginalMeasuredGHPSHuntHeatProperties_of_measured
#print axioms EIGS.exists_xiIdentifiedOriginalMeasuredGHPSHuntHeat_of_rules
#print axioms EIGS.exists_xiIdentifiedOriginalMeasuredGHPSHuntHeatPaperClock_of_rules
