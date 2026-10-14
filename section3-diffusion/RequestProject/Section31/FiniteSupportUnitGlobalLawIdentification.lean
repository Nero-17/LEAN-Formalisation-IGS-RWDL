import RequestProject.Section31.FiniteHorizonGlobalJ1Restriction
import RequestProject.Section31.FiniteSupportUnitJ1Transport

/-! The unit-interval J1 image of the finite support limit is exactly the
same global continuous law restricted and rescaled to the finite horizon.
Only its already identified function-valued restriction law is an input. -/

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal UniformConvergence
set_option maxHeartbeats 5000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
local instance unitGlobalStateBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance unitGlobalContinuousMeasurable : MeasurableSpace C(ℝ≥0, State) := borel _
local instance unitGlobalContinuousBorel : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩
local instance unitGlobalUnitMapMeasurable : MeasurableSpace C(UnitJ1Time, State) := borel _
local instance unitGlobalUnitMapBorel : BorelSpace C(UnitJ1Time, State) := ⟨rfl⟩
local instance unitGlobalIntervalBounded (horizon : ℝ≥0) : BoundedSpace (Icc (0 : ℝ) (horizon : ℝ)) :=
  ⟨Metric.isBounded_of_compactSpace⟩
local instance unitGlobalIntervalNonempty (horizon : ℝ≥0) : Nonempty (Icc (0 : ℝ) (horizon : ℝ)) :=
  ⟨⟨0, le_rfl, horizon.property⟩⟩
local instance unitGlobalIntervalMapMeasurable (horizon : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (horizon : ℝ), State) := borel _
local instance unitGlobalIntervalMapBorel (horizon : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (horizon : ℝ), State) := ⟨rfl⟩

def continuousPathToUnitCadlagJ1 (horizon : ℝ≥0) (path : C(ℝ≥0, State)) : UnitCadlagJ1Path State :=
  compactContinuousMapToCadlagJ1 (path.comp
    ⟨fun time : UnitJ1Time => ⟨(horizon : ℝ) * time.val, mul_nonneg horizon.property time.property.1⟩,
      (continuous_const.mul continuous_subtype_val).subtype_mk _⟩)

theorem continuousPathToUnitCadlagJ1_continuous (horizon : ℝ≥0) :
    Continuous (continuousPathToUnitCadlagJ1 (State := State) horizon) :=
  compactContinuousMapToCadlagJ1_lipschitz.continuous.comp (ContinuousMap.continuous_precomp _)

theorem finiteSupportPathToUnitCadlagJ1_law_eq_globalRestriction
    {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]
    [∀ level, MeasurableSpace (Vertex level)] [∀ level, MeasurableSingletonClass (Vertex level)]
    (horizon : ℝ≥0) (horizonPositive : 0 < horizon)
    (rates : ℕ → ℝ≥0) (embedding : ∀ level, Vertex level → State)
    (law : ProbabilityMeasure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding)))
    (lawContinuous : ∀ᵐ path ∂law.toMeasure, Continuous (UniformFun.toFun path.val))
    (globalLaw : ProbabilityMeasure C(ℝ≥0, State))
    (functionLawEquality :
      (law : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding))).map
        (fun path => UniformFun.toFun path.val) =
      (globalLaw : Measure C(ℝ≥0, State)).map
        (fun path => fun time : Icc (0 : ℝ) (horizon : ℝ) => path ⟨time.val, time.property.1⟩)) :
    ProbabilityMeasure.map law (finiteSupportPathToUnitCadlagJ1_measurable horizon horizonPositive
      (finiteHorizonStepPaths horizon rates embedding) (finiteHorizonStepPaths_isCadlag horizon rates embedding)).aemeasurable =
      ProbabilityMeasure.map globalLaw (continuousPathToUnitCadlagJ1_continuous horizon).measurable.aemeasurable := by
  classical
  let paths := finiteHorizonStepPaths horizon rates embedding
  let continuousPaths : Set (FiniteSupportPathSpace paths) :=
    {path | Continuous (UniformFun.toFun path.val)}
  have continuousPathsClosed : IsClosed continuousPaths :=
    (UniformFun.isClosed_setOf_continuous _).preimage continuous_subtype_val
  have subtypeEmbedding : MeasurableEmbedding (Subtype.val : continuousPaths → FiniteSupportPathSpace paths) :=
    MeasurableEmbedding.subtype_coe continuousPathsClosed.measurableSet
  let continuousPart : ProbabilityMeasure continuousPaths :=
    ⟨law.toMeasure.comap Subtype.val,
      subtypeEmbedding.isProbabilityMeasure_comap (by
        filter_upwards [lawContinuous] with path pathContinuous
        exact ⟨⟨path, pathContinuous⟩, rfl⟩)⟩
  have recovered : (continuousPart : Measure continuousPaths).map Subtype.val = law.toMeasure := by
    change (law.toMeasure.comap (Subtype.val : continuousPaths → FiniteSupportPathSpace paths)).map Subtype.val = _
    rw [map_comap_subtype_coe continuousPathsClosed.measurableSet]
    exact Measure.restrict_eq_self_of_ae_mem lawContinuous
  have liftMeasurable := (finiteSupportContinuousMapLift_isometry paths).continuous.measurable
  let liftedLaw := ProbabilityMeasure.map continuousPart liftMeasurable.aemeasurable
  let restrictedLaw := ProbabilityMeasure.map globalLaw
    (continuousPathFiniteHorizonRestriction_continuous horizon).measurable.aemeasurable
  have sourceFunctionMeasurable : Measurable (fun path : FiniteSupportPathSpace paths => UniformFun.toFun path.val) :=
    measurable_pi_lambda _ fun time => (finiteSupportPathSpace_continuous_eval paths time).measurable
  have continuousFunctionMeasurable : Measurable
      (fun path : C(Icc (0 : ℝ) (horizon : ℝ), State) => fun time => path time) :=
    measurable_pi_lambda _ fun time => (continuous_eval_const time).measurable
  have sameFunctions : (liftedLaw : Measure C(Icc (0 : ℝ) (horizon : ℝ), State)).map (fun path => fun time => path time) =
      (restrictedLaw : Measure C(Icc (0 : ℝ) (horizon : ℝ), State)).map (fun path => fun time => path time) := by
    change ((continuousPart : Measure continuousPaths).map (finiteSupportContinuousMapLift paths)).map _ =
      ((globalLaw : Measure C(ℝ≥0, State)).map (continuousPathFiniteHorizonRestriction horizon)).map _
    rw [Measure.map_map continuousFunctionMeasurable liftMeasurable,
      Measure.map_map continuousFunctionMeasurable (continuousPathFiniteHorizonRestriction_continuous horizon).measurable]
    calc
      _ = ((continuousPart : Measure continuousPaths).map Subtype.val).map
          (fun path : FiniteSupportPathSpace paths => UniformFun.toFun path.val) := by
        rw [Measure.map_map sourceFunctionMeasurable subtypeEmbedding.measurable]
        rfl
      _ = _ := by rw [recovered, functionLawEquality]; rfl
  let denseTimes := TopologicalSpace.denseSeq (Icc (0 : ℝ) (horizon : ℝ))
  have denseEmbedding := compactContinuousMap_denseEvaluation_measurableEmbedding
    (State := State) denseTimes (TopologicalSpace.denseRange_denseSeq _)
  have denseRestrictionMeasurable : Measurable
      (fun function : Icc (0 : ℝ) (horizon : ℝ) → State => fun index : ℕ => function (denseTimes index)) :=
    measurable_pi_lambda _ fun index => measurable_pi_apply (denseTimes index)
  have sameDense := congrArg (Measure.map (fun function : Icc (0 : ℝ) (horizon : ℝ) → State =>
    fun index : ℕ => function (denseTimes index))) sameFunctions
  rw [Measure.map_map denseRestrictionMeasurable continuousFunctionMeasurable,
    Measure.map_map denseRestrictionMeasurable continuousFunctionMeasurable] at sameDense
  have liftedEquality : liftedLaw = restrictedLaw := by
    apply ProbabilityMeasure.toMeasure_injective
    exact denseEmbedding.map_injective sameDense
  let toUnit : C(Icc (0 : ℝ) (horizon : ℝ), State) → UnitCadlagJ1Path State := fun path =>
    compactContinuousMapToCadlagJ1 (path.comp ⟨unitIntervalScale horizon, unitIntervalScale_continuous horizon⟩)
  have toUnitContinuous : Continuous toUnit :=
    compactContinuousMapToCadlagJ1_lipschitz.continuous.comp (ContinuousMap.continuous_precomp _)
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  calc
    _ = ((continuousPart : Measure continuousPaths).map Subtype.val).map
        (finiteSupportPathToUnitCadlagJ1 horizon horizonPositive paths (finiteHorizonStepPaths_isCadlag _ _ _)) := by
      rw [recovered]
    _ = (continuousPart : Measure continuousPaths).map (toUnit ∘ finiteSupportContinuousMapLift paths) := by
      rw [Measure.map_map (finiteSupportPathToUnitCadlagJ1_measurable _ _ _ _) subtypeEmbedding.measurable]
      rfl
    _ = (liftedLaw : Measure C(Icc (0 : ℝ) (horizon : ℝ), State)).map toUnit := by
      change _ = ((continuousPart : Measure continuousPaths).map (finiteSupportContinuousMapLift paths)).map toUnit
      rw [Measure.map_map toUnitContinuous.measurable liftMeasurable]
    _ = (restrictedLaw : Measure C(Icc (0 : ℝ) (horizon : ℝ), State)).map toUnit := by rw [liftedEquality]
    _ = _ := by
      change ((globalLaw : Measure C(ℝ≥0, State)).map (continuousPathFiniteHorizonRestriction horizon)).map toUnit = _
      rw [Measure.map_map toUnitContinuous.measurable (continuousPathFiniteHorizonRestriction_continuous horizon).measurable]
      rfl

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPathToUnitCadlagJ1_continuous
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathToUnitCadlagJ1_law_eq_globalRestriction
