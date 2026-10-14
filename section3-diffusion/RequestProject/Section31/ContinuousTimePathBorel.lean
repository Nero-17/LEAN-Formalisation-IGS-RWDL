import RequestProject.Section31.IntegerHorizonPathReconstruction
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! The evaluation measurable space on continuous nonnegative-real-time
paths agrees, under the canonical equivalence, with the Borel measurable
space of the compact-open topology. A countable dense set of evaluations
already generates this Borel measurable space. Completeness and countability
of compact convergence come from the locally compact, sigma-compact time
domain. Compact-open convergence is locally uniform convergence.

This file proves a measurable-space identification. It does not assert
measurability of a family of path laws in its starting point or Hunt properties. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal Uniformity
noncomputable section
set_option maxHeartbeats 4000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance continuousTimeContinuousMapMeasurableSpace :
    MeasurableSpace C(ℝ≥0, State) := borel _

local instance continuousTimeContinuousMapBorelSpace :
    BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

theorem continuousTimeContinuousMap_polishSpace : PolishSpace C(ℝ≥0, State) :=
  inferInstance

def continuousTimePathEquivContinuousMap : ContinuousTimePath State ≃ C(ℝ≥0, State) where
  toFun path := ⟨path.val, path.property⟩
  invFun path := ⟨path, path.continuous⟩
  left_inv path := rfl
  right_inv path := rfl

theorem continuousMap_denseEvaluation_measurableEmbedding
    (denseTimes : ℕ → ℝ≥0) (timesDense : DenseRange denseTimes) :
    MeasurableEmbedding (fun path : C(ℝ≥0, State) => fun index : ℕ => path (denseTimes index)) := by
  have evaluationContinuous : Continuous
      (fun path : C(ℝ≥0, State) => fun index : ℕ => path (denseTimes index)) :=
    continuous_pi fun index => continuous_eval_const (denseTimes index)
  have evaluationInjective : Function.Injective
      (fun path : C(ℝ≥0, State) => fun index : ℕ => path (denseTimes index)) := by
    intro firstPath secondPath sameEvaluations
    apply DFunLike.coe_injective
    apply Continuous.ext_on timesDense firstPath.continuous secondPath.continuous
    rintro time ⟨index, rfl⟩
    exact congrFun sameEvaluations index
  exact evaluationContinuous.measurableEmbedding evaluationInjective

theorem continuousMap_borel_eq_comap_denseEvaluation
    (denseTimes : ℕ → ℝ≥0) (timesDense : DenseRange denseTimes) :
    borel C(ℝ≥0, State) = MeasurableSpace.comap
      (fun path : C(ℝ≥0, State) => fun index : ℕ => path (denseTimes index))
      (inferInstance : MeasurableSpace (ℕ → State)) :=
  (continuousMap_denseEvaluation_measurableEmbedding denseTimes timesDense).comap_eq.symm

def continuousTimePathMeasurableEquivContinuousMap :
    ContinuousTimePath State ≃ᵐ C(ℝ≥0, State) where
  toEquiv := continuousTimePathEquivContinuousMap
  measurable_toFun := by
    apply (continuousMap_denseEvaluation_measurableEmbedding
      (TopologicalSpace.denseSeq ℝ≥0) (TopologicalSpace.denseRange_denseSeq ℝ≥0)).measurable_comp_iff.mp
    exact measurable_pi_lambda _ fun index =>
      (measurable_pi_apply (TopologicalSpace.denseSeq ℝ≥0 index)).comp measurable_subtype_coe
  measurable_invFun := by
    apply Measurable.subtype_mk
    exact measurable_pi_lambda _ fun time => (continuous_eval_const time).measurable

theorem continuousTimePath_evaluation_measurableSpace_eq_compactOpen :
    (inferInstance : MeasurableSpace (ContinuousTimePath State)) =
      MeasurableSpace.comap (continuousTimePathEquivContinuousMap (State := State))
        (borel C(ℝ≥0, State)) :=
  (continuousTimePathMeasurableEquivContinuousMap (State := State)).measurableEmbedding.comap_eq.symm

theorem continuousTimePath_compactOpen_tendsto_iff_locallyUniformly
    {Index : Type*} (filter : Filter Index) (paths : Index → ContinuousTimePath State)
    (path : ContinuousTimePath State) :
    Tendsto (fun index => continuousTimePathEquivContinuousMap (paths index)) filter
      (𝓝 (continuousTimePathEquivContinuousMap path)) ↔
      TendstoLocallyUniformly (fun index => (paths index).val) path.val filter :=
  ContinuousMap.tendsto_iff_tendstoLocallyUniformly

def continuousTimePathLawToCompactOpen (law : ProbabilityMeasure (ContinuousTimePath State)) :
    ProbabilityMeasure C(ℝ≥0, State) :=
  law.map (continuousTimePathMeasurableEquivContinuousMap (State := State)).measurable.aemeasurable

theorem continuousTimePathLawToCompactOpen_finite_evaluations
    (law : ProbabilityMeasure (ContinuousTimePath State))
    (dimension : ℕ) (times : Fin dimension → ℝ≥0) :
    (continuousTimePathLawToCompactOpen law : Measure C(ℝ≥0, State)).map
      (fun path => fun index => path (times index)) =
        (law : Measure (ContinuousTimePath State)).map
          (fun path => fun index => path.val (times index)) := by
  change ((law : Measure (ContinuousTimePath State)).map
    (continuousTimePathMeasurableEquivContinuousMap (State := State))).map
      (fun path => fun index => path (times index)) = _
  rw [Measure.map_map
    (measurable_pi_lambda _ fun index => (continuous_eval_const (times index)).measurable)
    (continuousTimePathMeasurableEquivContinuousMap (State := State)).measurable]
  rfl

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousTimeContinuousMap_polishSpace
#print axioms IGS.Sec31.DiscreteMarkov.continuousMap_borel_eq_comap_denseEvaluation
#print axioms IGS.Sec31.DiscreteMarkov.continuousTimePathMeasurableEquivContinuousMap
#print axioms IGS.Sec31.DiscreteMarkov.continuousTimePath_evaluation_measurableSpace_eq_compactOpen
#print axioms IGS.Sec31.DiscreteMarkov.continuousTimePath_compactOpen_tendsto_iff_locallyUniformly
#print axioms IGS.Sec31.DiscreteMarkov.continuousTimePathLawToCompactOpen_finite_evaluations
