import RequestProject.Section31.FiniteGraphExponentialJ1PathLaw
import RequestProject.Section31.FiniteSupportUnitJ1Transport
import RequestProject.Section31.ProbabilityConstructedCouplingWeakLimit

/-! Explicit finite-graph holding laws have the same weak limit as their
floor paths under the actual product-sample coupling. The limit is the
mapped floor-law limit, so no separate target-law witness is selected. -/

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open IGS.Sec31.DiscreteMarkov EIGS
open scoped Topology NNReal
set_option maxHeartbeats 6000000

variable {State : Type} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
local instance exponentialUniformStateBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩

theorem finiteGraphExponentialJ1Laws_tendsto_of_floor_coupling
    (Vertex : ℕ → Type) [∀ level, Fintype (Vertex level)] [∀ level, DecidableEq (Vertex level)]
    [∀ level, MeasurableSpace (Vertex level)] [∀ level, MeasurableSingletonClass (Vertex level)]
    (graphs : ∀ level, SimpleGraph (Vertex level)) [∀ level, DecidableRel (graphs level).Adj]
    (degreePositive : ∀ level vertex, 0 < (graphs level).degree vertex)
    (initial : ∀ level, ProbabilityMeasure (Vertex level))
    (embedding : ∀ level, Vertex level → State) (rates : ℕ → ℝ≥0) (ratesPositive : ∀ level, 0 < rates level)
    (horizon : ℝ≥0) (horizonPositive : 0 < horizon)
    (limit : ProbabilityMeasure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding)))
    (floorConverges : Tendsto (finiteHorizonStepLaw horizon rates embedding
      (fun level => finiteGraphTransitionKernel (graphs level) (degreePositive level)) initial) atTop (𝓝 limit))
    (sampleCoupling : ∀ radius error : ℝ, 0 < radius → 0 < error → ∀ᶠ level in atTop,
      ∃ bad : Set ((ℕ → Vertex level) × (ℕ → ℝ)),
        MeasurableSet bad ∧
        (finiteGraphExponentialSampleLaw (graphs level) (degreePositive level) (initial level)).real bad ≤ error ∧
        ∀ sample ∉ bad, ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
          dist (embedding level (holdingTimePath sample.1 sample.2 ((rates level : ℝ) * time)))
            (embedding level (sample.1 ⌊(rates level : ℝ) * time⌋₊)) ≤ radius) :
    Tendsto (fun level => (
      finiteGraphExponentialJ1Law (graphs level) (degreePositive level) (initial level) (embedding level)
        ((rates level : ℝ) * horizon) (mul_pos (ratesPositive level) (by exact_mod_cast horizonPositive)) :
          ProbabilityMeasure (UnitCadlagJ1Path State))) atTop
      (𝓝 (ProbabilityMeasure.map limit (finiteSupportPathToUnitCadlagJ1_measurable horizon horizonPositive
        (finiteHorizonStepPaths horizon rates embedding) (finiteHorizonStepPaths_isCadlag horizon rates embedding)).aemeasurable)) := by
  classical
  have horizonPositiveNNReal : (0 : ℝ≥0) < horizon := by exact_mod_cast horizonPositive
  let paths := finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding
  let toUnit := finiteSupportPathToUnitCadlagJ1 (horizon : ℝ≥0) horizonPositiveNNReal paths
    (finiteHorizonStepPaths_isCadlag (horizon : ℝ≥0) rates embedding)
  have toUnitMeasurable : Measurable toUnit := finiteSupportPathToUnitCadlagJ1_measurable
    (horizon : ℝ≥0) horizonPositiveNNReal paths (finiteHorizonStepPaths_isCadlag _ _ _)
  let kernels := fun level => finiteGraphTransitionKernel (graphs level) (degreePositive level)
  let floorLaws := finiteHorizonStepLaw (horizon : ℝ≥0) rates embedding kernels initial
  let sourceLaws := fun level => ProbabilityMeasure.map (floorLaws level) toUnitMeasurable.aemeasurable
  let targetLaws := fun level => finiteGraphExponentialJ1Law (graphs level) (degreePositive level) (initial level)
    (embedding level) ((rates level : ℝ) * horizon) (mul_pos (ratesPositive level) (by exact_mod_cast horizonPositive))
  let joint := fun level => finiteGraphExponentialSampleLaw (graphs level) (degreePositive level) (initial level)
  let source := fun level (sample : (ℕ → Vertex level) × (ℕ → ℝ)) =>
    toUnit (finiteHorizonStepMap (horizon : ℝ≥0) rates embedding level sample.1)
  let target := fun level => exponentialHoldingJ1Sample (embedding level)
    ((rates level : ℝ) * horizon) (mul_pos (ratesPositive level) (by exact_mod_cast horizonPositive))
  have sourceMeasurable (level : ℕ) : Measurable (source level) := toUnitMeasurable.comp
    ((finiteHorizonStepMap_measurable (horizon : ℝ≥0) rates embedding level).comp measurable_fst)
  have targetMeasurable (level : ℕ) : AEMeasurable (target level) (joint level) :=
    exponentialHoldingJ1Sample_aemeasurable _ _ _ _ _ _
  have sourceMarginal (level : ℕ) : (joint level).map (source level) = (sourceLaws level : Measure _) := by
    change (joint level).map ((toUnit ∘ finiteHorizonStepMap (horizon : ℝ≥0) rates embedding level) ∘ Prod.fst) = _
    rw [← Measure.map_map (toUnitMeasurable.comp (finiteHorizonStepMap_measurable _ _ _ _)) measurable_fst,
      finiteGraphExponentialSampleLaw_discrete_marginal]
    rw [← Measure.map_map toUnitMeasurable (finiteHorizonStepMap_measurable _ _ _ _)]
    change Measure.map toUnit
      ((pathLaw (kernels level) (initial level)).map (finiteHorizonStepMap horizon rates embedding level)) =
        Measure.map toUnit (floorLaws level : Measure _)
    exact congrArg (Measure.map toUnit)
      (finiteHorizonStepLaw_eq_map horizon rates embedding kernels initial level).symm
  have targetMarginal (level : ℕ) : (joint level).map (target level) = (targetLaws level : Measure _) := rfl
  let samples := fun level => (⟨joint level, inferInstance⟩ : ProbabilityMeasure ((ℕ → Vertex level) × (ℕ → ℝ)))
  have mappedConverges : Tendsto sourceLaws atTop
      (𝓝 (ProbabilityMeasure.map limit toUnitMeasurable.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ floorConverges
      (finiteSupportPathToUnitCadlagJ1_lipschitz horizon horizonPositiveNNReal paths
        (finiteHorizonStepPaths_isCadlag _ _ _)).continuous
  have sourceEquality : (fun level => ProbabilityMeasure.map (samples level) (sourceMeasurable level).aemeasurable) =
      sourceLaws := by
    funext level
    apply ProbabilityMeasure.toMeasure_injective
    exact sourceMarginal level
  have targetEquality : (fun level => ProbabilityMeasure.map (samples level) (targetMeasurable level)) = targetLaws := rfl
  rw [← sourceEquality] at mappedConverges
  change Tendsto targetLaws atTop (𝓝 (ProbabilityMeasure.map limit toUnitMeasurable.aemeasurable))
  rw [← targetEquality]
  apply IGS.Sec31.probability_maps_same_limit_of_constructed_coupling samples source target
    (fun level => (sourceMeasurable level).aemeasurable) targetMeasurable _ _ mappedConverges
  intro radius error radiusPositive errorPositive
  filter_upwards [sampleCoupling radius error radiusPositive errorPositive] with level coupling
  obtain ⟨bad, badMeasurable, badBound, close⟩ := coupling
  refine ⟨bad, badMeasurable, badBound, ?_⟩
  filter_upwards [finiteGraphExponentialSampleLaw_clock_regular (graphs level) (degreePositive level) (initial level)]
    with sample regular
  intro outside
  change skorokhodJ1Distance (target level sample).val.toFun (source level sample).val.toFun ≤ radius
  apply (skorokhodJ1Distance_le_uniform _ _).trans
  apply (UniformFun.dist_le radiusPositive.le).mpr
  intro time
  have timeNonnegative : 0 ≤ (horizon : ℝ) * time.val := mul_nonneg horizon.property time.property.1
  have timeBound : (horizon : ℝ) * time.val ≤ horizon := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left time.property.2 horizon.property
  have bound := close sample outside ((horizon : ℝ) * time.val) timeNonnegative timeBound
  have targetEvaluation : (target level sample).val.toFun time =
      embedding level (holdingTimePath sample.1 sample.2 ((rates level : ℝ) * ((horizon : ℝ) * time.val))) := by
    change (exponentialHoldingJ1Sample (embedding level) ((rates level : ℝ) * horizon) _ sample).val.toFun time = _
    simp only [exponentialHoldingJ1Sample, dif_pos regular, unitHoldingCadlagPath, holdingTimePath, mul_assoc]
  have sourceEvaluation : (source level sample).val.toFun time =
      embedding level (sample.1 ⌊((horizon : ℝ) * time.val) * (rates level : ℝ)⌋₊) := by
    change UniformFun.toFun (finiteHorizonStepMap horizon rates embedding level sample.1).val
      (unitIntervalScale horizon time) = _
    exact finiteHorizonStepMap_apply horizon rates embedding level sample.1 (unitIntervalScale horizon time)
  change dist ((target level sample).val.toFun time) ((source level sample).val.toFun time) ≤ radius
  rw [targetEvaluation, sourceEvaluation, mul_comm ((horizon : ℝ) * time.val) (rates level : ℝ)]
  exact bound

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialJ1Laws_tendsto_of_floor_coupling

