import RequestProject.Section31.FiniteSupportCadlagJ1Transport
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Identify a continuous limit's J1 law with its already identified
function-valued law. Equality is first proved on ordinary continuous maps
through a countable dense evaluation embedding, then pushed to J1. No
measurable embedding of arbitrary cadlag paths into evaluations, D Polish
space, or target J1 law identity is assumed. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal UniformConvergence
noncomputable section

variable {Time State : Type*} [LinearOrder Time] [MetricSpace Time] [CompactSpace Time]
variable [MetricSpace State] [CompactSpace State] [MeasurableSpace State] [BorelSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]

local instance continuousJ1BridgeTimeBounded : BoundedSpace Time := ⟨Metric.isBounded_of_compactSpace⟩
local instance continuousJ1BridgeStateBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance continuousJ1BridgeMapMeasurable : MeasurableSpace C(Time, State) := borel _
local instance continuousJ1BridgeMapBorel : BorelSpace C(Time, State) := ⟨rfl⟩
local instance continuousJ1BridgeTargetMeasurable : MeasurableSpace (CadlagJ1Path Time State) := borel _
local instance continuousJ1BridgeTargetBorel : BorelSpace (CadlagJ1Path Time State) := ⟨rfl⟩

def compactContinuousMapToCadlagJ1 (path : C(Time, State)) : CadlagJ1Path Time State :=
  ⟨⟨path⟩, path.continuous.isCadlagPath⟩

theorem compactContinuousMapToCadlagJ1_lipschitz :
    LipschitzWith 1 (compactContinuousMapToCadlagJ1 (Time := Time) (State := State)) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  change skorokhodJ1Distance (fun time => first time) (fun time => second time) ≤ (1 : ℝ) * dist first second
  rw [one_mul]
  calc
    _ ≤ dist (UniformFun.ofFun (fun time => first time)) (UniformFun.ofFun (fun time => second time)) :=
      skorokhodJ1Distance_le_uniform _ _
    _ = dist first second := by rw [UniformFun.dist_def, ContinuousMap.dist_eq_iSup]

theorem compactContinuousMap_denseEvaluation_measurableEmbedding
    (denseTimes : ℕ → Time) (timesDense : DenseRange denseTimes) :
    MeasurableEmbedding (fun path : C(Time, State) => fun index : ℕ => path (denseTimes index)) := by
  have evaluationContinuous : Continuous (fun path : C(Time, State) => fun index : ℕ => path (denseTimes index)) :=
    continuous_pi fun index => continuous_eval_const (denseTimes index)
  have evaluationInjective : Function.Injective (fun path : C(Time, State) => fun index : ℕ => path (denseTimes index)) := by
    intro first second equality
    apply DFunLike.coe_injective
    apply Continuous.ext_on timesDense first.continuous second.continuous
    rintro time ⟨index, rfl⟩
    exact congrFun equality index
  exact evaluationContinuous.measurableEmbedding evaluationInjective

def finiteSupportContinuousMapLift
    (paths : (level : ℕ) → History level → Time → State)
    (path : {path : FiniteSupportPathSpace paths // Continuous (UniformFun.toFun path.val)}) : C(Time, State) :=
  ⟨UniformFun.toFun path.val.val, path.property⟩

theorem finiteSupportContinuousMapLift_isometry
    (paths : (level : ℕ) → History level → Time → State) :
    Isometry (finiteSupportContinuousMapLift paths) := by
  apply isometry_iff_dist_eq.mpr
  intro first second
  change dist (finiteSupportContinuousMapLift paths first) (finiteSupportContinuousMapLift paths second) =
    dist first.val second.val
  rw [ContinuousMap.dist_eq_iSup, finiteSupportPathSpace_dist]
  rfl

theorem finiteSupportPath_j1Law_eq_continuousLaw
    [Nonempty Time]
    (paths : (level : ℕ) → History level → Time → State)
    (supportsCadlag : ∀ level history, IsCadlagPath (paths level history))
    (law : ProbabilityMeasure (FiniteSupportPathSpace paths))
    (lawContinuous : ∀ᵐ path ∂(law : Measure (FiniteSupportPathSpace paths)), Continuous (UniformFun.toFun path.val))
    (continuousLaw : ProbabilityMeasure C(Time, State))
    (functionLawEquality :
      (law : Measure (FiniteSupportPathSpace paths)).map (fun path => UniformFun.toFun path.val) =
        (continuousLaw : Measure C(Time, State)).map (fun path => fun time => path time)) :
    law.map (finiteSupportPathSpaceToCadlagJ1_continuous paths supportsCadlag).measurable.aemeasurable =
      continuousLaw.map compactContinuousMapToCadlagJ1_lipschitz.continuous.measurable.aemeasurable := by
  let continuousPaths : Set (FiniteSupportPathSpace paths) :=
    {path | Continuous (UniformFun.toFun path.val)}
  have continuousPathsClosed : IsClosed continuousPaths :=
    (UniformFun.isClosed_setOf_continuous Time).preimage continuous_subtype_val
  have subtypeEmbedding : MeasurableEmbedding (Subtype.val : continuousPaths → FiniteSupportPathSpace paths) :=
    MeasurableEmbedding.subtype_coe continuousPathsClosed.measurableSet
  let continuousPart : ProbabilityMeasure continuousPaths :=
    ⟨(law : Measure (FiniteSupportPathSpace paths)).comap Subtype.val,
      subtypeEmbedding.isProbabilityMeasure_comap (by
        filter_upwards [lawContinuous] with path pathContinuous
        exact ⟨⟨path, pathContinuous⟩, rfl⟩)⟩
  have recovered : (continuousPart : Measure continuousPaths).map Subtype.val =
      (law : Measure (FiniteSupportPathSpace paths)) := by
    change ((law : Measure (FiniteSupportPathSpace paths)).comap
      (Subtype.val : continuousPaths → FiniteSupportPathSpace paths)).map Subtype.val = _
    rw [map_comap_subtype_coe continuousPathsClosed.measurableSet]
    exact Measure.restrict_eq_self_of_ae_mem lawContinuous
  have liftMeasurable := (finiteSupportContinuousMapLift_isometry paths).continuous.measurable
  let liftedLaw : ProbabilityMeasure C(Time, State) := continuousPart.map liftMeasurable.aemeasurable
  have sourceFunctionMeasurable : Measurable (fun path : FiniteSupportPathSpace paths => UniformFun.toFun path.val) :=
    measurable_pi_lambda _ fun time => (finiteSupportPathSpace_continuous_eval paths time).measurable
  have continuousFunctionMeasurable : Measurable (fun path : C(Time, State) => fun time => path time) :=
    measurable_pi_lambda _ fun time => (continuous_eval_const time).measurable
  have sameFunctions : (liftedLaw : Measure C(Time, State)).map (fun path => fun time => path time) =
      (continuousLaw : Measure C(Time, State)).map (fun path => fun time => path time) := by
    change ((continuousPart : Measure continuousPaths).map (finiteSupportContinuousMapLift paths)).map
        (fun path => fun time => path time) = _
    rw [Measure.map_map continuousFunctionMeasurable liftMeasurable]
    calc
      _ = ((continuousPart : Measure continuousPaths).map Subtype.val).map
          (fun path : FiniteSupportPathSpace paths => UniformFun.toFun path.val) := by
        rw [Measure.map_map sourceFunctionMeasurable subtypeEmbedding.measurable]
        rfl
      _ = _ := by rw [recovered, functionLawEquality]
  let denseTimes := TopologicalSpace.denseSeq Time
  have denseEmbedding := compactContinuousMap_denseEvaluation_measurableEmbedding
    (State := State) denseTimes (TopologicalSpace.denseRange_denseSeq Time)
  have denseRestrictionMeasurable : Measurable (fun function : Time → State => fun index : ℕ => function (denseTimes index)) :=
    measurable_pi_lambda _ fun index => measurable_pi_apply (denseTimes index)
  have sameDense := congrArg (Measure.map (fun function : Time → State => fun index : ℕ => function (denseTimes index))) sameFunctions
  rw [Measure.map_map denseRestrictionMeasurable continuousFunctionMeasurable,
    Measure.map_map denseRestrictionMeasurable continuousFunctionMeasurable] at sameDense
  have liftedEquality : liftedLaw = continuousLaw := by
    apply ProbabilityMeasure.toMeasure_injective
    exact denseEmbedding.map_injective sameDense
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  calc
    _ = ((continuousPart : Measure continuousPaths).map Subtype.val).map
        (finiteSupportPathSpaceToCadlagJ1 paths supportsCadlag) := by rw [recovered]
    _ = (continuousPart : Measure continuousPaths).map
        (compactContinuousMapToCadlagJ1 ∘ finiteSupportContinuousMapLift paths) := by
      rw [Measure.map_map (finiteSupportPathSpaceToCadlagJ1_continuous paths supportsCadlag).measurable
        subtypeEmbedding.measurable]
      rfl
    _ = (liftedLaw : Measure C(Time, State)).map compactContinuousMapToCadlagJ1 := by
      change _ = ((continuousPart : Measure continuousPaths).map (finiteSupportContinuousMapLift paths)).map
        compactContinuousMapToCadlagJ1
      rw [Measure.map_map compactContinuousMapToCadlagJ1_lipschitz.continuous.measurable liftMeasurable]
    _ = _ := by rw [liftedEquality]

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.compactContinuousMapToCadlagJ1_lipschitz
#print axioms IGS.Sec31.DiscreteMarkov.compactContinuousMap_denseEvaluation_measurableEmbedding
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportContinuousMapLift_isometry
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPath_j1Law_eq_continuousLaw
