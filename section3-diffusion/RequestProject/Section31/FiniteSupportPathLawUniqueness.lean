import RequestProject.Section31.FiniteSupportUniformPathSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic

/-! Dense finite evaluations determine laws supported on continuous paths.
The common carrier also contains discontinuous finite-level paths, so the
restriction to a dense set of times is used only on its closed continuous
subtype. Each probability measure is first transported to that subtype. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter
open scoped UniformConvergence Topology Classical NNReal ENNReal

variable {Time State : Type*} [TopologicalSpace Time]
variable [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]

theorem finiteSupportPath_law_eq_of_dense_finite_evaluations
    (paths : (level : ℕ) → History level → Time → State)
    (denseTimes : ℕ → Time) (timesDense : DenseRange denseTimes)
    (first second : ProbabilityMeasure (FiniteSupportPathSpace paths))
    (firstContinuous : ∀ᵐ path ∂(first : Measure (FiniteSupportPathSpace paths)),
      Continuous (UniformFun.toFun path.val))
    (secondContinuous : ∀ᵐ path ∂(second : Measure (FiniteSupportPathSpace paths)),
      Continuous (UniformFun.toFun path.val))
    (finiteEvaluations : ∀ (dimension : ℕ) (indices : Fin dimension → ℕ),
      (first : Measure (FiniteSupportPathSpace paths)).map
        (fun path => fun index => UniformFun.toFun path.val (denseTimes (indices index))) =
      (second : Measure (FiniteSupportPathSpace paths)).map
        (fun path => fun index => UniformFun.toFun path.val (denseTimes (indices index)))) :
    first = second := by
  classical
  let continuousPaths : Set (FiniteSupportPathSpace paths) :=
    {path | Continuous (UniformFun.toFun path.val)}
  have uniformContinuousPathsClosed :
      IsClosed {path : Time →ᵤ State | Continuous (UniformFun.toFun path)} :=
    UniformFun.isClosed_setOf_continuous Time
  have continuousPathsClosed : IsClosed continuousPaths :=
    uniformContinuousPathsClosed.preimage continuous_subtype_val
  letI : PolishSpace continuousPaths := continuousPathsClosed.polishSpace
  have subtypeEmbedding : MeasurableEmbedding
      (Subtype.val : continuousPaths → FiniteSupportPathSpace paths) :=
    MeasurableEmbedding.subtype_coe continuousPathsClosed.measurableSet
  let firstContinuousLaw : ProbabilityMeasure continuousPaths :=
    ⟨(first : Measure (FiniteSupportPathSpace paths)).comap Subtype.val,
      subtypeEmbedding.isProbabilityMeasure_comap (by
        filter_upwards [firstContinuous] with path pathContinuous
        exact ⟨⟨path, pathContinuous⟩, rfl⟩)⟩
  let secondContinuousLaw : ProbabilityMeasure continuousPaths :=
    ⟨(second : Measure (FiniteSupportPathSpace paths)).comap Subtype.val,
      subtypeEmbedding.isProbabilityMeasure_comap (by
        filter_upwards [secondContinuous] with path pathContinuous
        exact ⟨⟨path, pathContinuous⟩, rfl⟩)⟩
  have firstRecovered : (firstContinuousLaw : Measure continuousPaths).map Subtype.val =
      (first : Measure (FiniteSupportPathSpace paths)) := by
    change ((first : Measure (FiniteSupportPathSpace paths)).comap
      (Subtype.val : continuousPaths → FiniteSupportPathSpace paths)).map Subtype.val = _
    rw [map_comap_subtype_coe continuousPathsClosed.measurableSet]
    exact Measure.restrict_eq_self_of_ae_mem
      (show ∀ᵐ path ∂(first : Measure (FiniteSupportPathSpace paths)),
        path ∈ continuousPaths from firstContinuous)
  have secondRecovered : (secondContinuousLaw : Measure continuousPaths).map Subtype.val =
      (second : Measure (FiniteSupportPathSpace paths)) := by
    change ((second : Measure (FiniteSupportPathSpace paths)).comap
      (Subtype.val : continuousPaths → FiniteSupportPathSpace paths)).map Subtype.val = _
    rw [map_comap_subtype_coe continuousPathsClosed.measurableSet]
    exact Measure.restrict_eq_self_of_ae_mem
      (show ∀ᵐ path ∂(second : Measure (FiniteSupportPathSpace paths)),
        path ∈ continuousPaths from secondContinuous)
  let restriction : continuousPaths → ℕ → State := fun path index =>
    UniformFun.toFun path.val.val (denseTimes index)
  have restrictionContinuous : Continuous restriction :=
    continuous_pi fun index =>
      (finiteSupportPathSpace_continuous_eval paths (denseTimes index)).comp continuous_subtype_val
  have restrictionInjective : Function.Injective restriction := by
    intro firstPath secondPath sameRestrictions
    apply Subtype.ext
    apply Subtype.ext
    apply UniformFun.toFun.injective
    apply Continuous.ext_on timesDense firstPath.property secondPath.property
    rintro time ⟨index, rfl⟩
    exact congrFun sameRestrictions index
  have restrictionEmbedding : MeasurableEmbedding restriction :=
    restrictionContinuous.measurableEmbedding restrictionInjective
  have finiteSetEvaluations : ∀ indices : Finset ℕ,
      (first : Measure (FiniteSupportPathSpace paths)).map
        (fun path => fun index : indices => UniformFun.toFun path.val (denseTimes index.val)) =
      (second : Measure (FiniteSupportPathSpace paths)).map
        (fun path => fun index : indices => UniformFun.toFun path.val (denseTimes index.val)) := by
    intro indices
    let enumeration : indices ≃ Fin (Fintype.card indices) := Fintype.equivFin indices
    let evaluation : FiniteSupportPathSpace paths → Fin (Fintype.card indices) → State :=
      fun path index => UniformFun.toFun path.val (denseTimes (enumeration.symm index).val)
    let reorder : (Fin (Fintype.card indices) → State) → indices → State :=
      fun values index => values (enumeration index)
    have evaluationMeasurable : Measurable evaluation :=
      (continuous_pi fun index => finiteSupportPathSpace_continuous_eval paths
        (denseTimes (enumeration.symm index).val)).measurable
    have reorderMeasurable : Measurable reorder :=
      measurable_pi_lambda _ fun index => measurable_pi_apply (enumeration index)
    have same := congrArg (Measure.map reorder)
      (finiteEvaluations (Fintype.card indices) (fun index => (enumeration.symm index).val))
    change ((first : Measure (FiniteSupportPathSpace paths)).map evaluation).map reorder =
      ((second : Measure (FiniteSupportPathSpace paths)).map evaluation).map reorder at same
    rw [Measure.map_map reorderMeasurable evaluationMeasurable,
      Measure.map_map reorderMeasurable evaluationMeasurable] at same
    have reorderedEvaluation : reorder ∘ evaluation =
        fun path => fun index : indices => UniformFun.toFun path.val (denseTimes index.val) := by
      funext path index
      simp only [reorder, evaluation, Function.comp_apply, Equiv.symm_apply_apply]
    simpa only [reorderedEvaluation] using same
  have projectedSame : ∀ indices : Finset ℕ,
      ((firstContinuousLaw : Measure continuousPaths).map restriction).map indices.restrict =
      ((secondContinuousLaw : Measure continuousPaths).map restriction).map indices.restrict := by
    intro indices
    have projectionMeasurable : Measurable (indices.restrict : (ℕ → State) → indices → State) :=
      measurable_pi_lambda _ fun index => measurable_pi_apply index.val
    have evaluationMeasurable : Measurable
        (fun path : FiniteSupportPathSpace paths =>
          fun index : indices => UniformFun.toFun path.val (denseTimes index.val)) :=
      (continuous_pi fun (index : indices) =>
        finiteSupportPathSpace_continuous_eval paths (denseTimes index.val)).measurable
    calc
      ((firstContinuousLaw : Measure continuousPaths).map restriction).map indices.restrict =
          ((firstContinuousLaw : Measure continuousPaths).map Subtype.val).map
            (fun path => fun index : indices => UniformFun.toFun path.val (denseTimes index.val)) := by
        rw [Measure.map_map projectionMeasurable restrictionEmbedding.measurable,
          Measure.map_map evaluationMeasurable subtypeEmbedding.measurable]
        rfl
      _ = (first : Measure (FiniteSupportPathSpace paths)).map
          (fun path => fun index : indices => UniformFun.toFun path.val (denseTimes index.val)) := by
        rw [firstRecovered]
      _ = (second : Measure (FiniteSupportPathSpace paths)).map
          (fun path => fun index : indices => UniformFun.toFun path.val (denseTimes index.val)) :=
        finiteSetEvaluations indices
      _ = ((secondContinuousLaw : Measure continuousPaths).map Subtype.val).map
          (fun path => fun index : indices => UniformFun.toFun path.val (denseTimes index.val)) := by
        rw [secondRecovered]
      _ = ((secondContinuousLaw : Measure continuousPaths).map restriction).map indices.restrict := by
        rw [Measure.map_map evaluationMeasurable subtypeEmbedding.measurable,
          Measure.map_map projectionMeasurable restrictionEmbedding.measurable]
        rfl
  have sameRestrictions : (firstContinuousLaw : Measure continuousPaths).map restriction =
      (secondContinuousLaw : Measure continuousPaths).map restriction := by
    apply IsProjectiveLimit.unique
      (P := fun indices : Finset ℕ =>
        ((firstContinuousLaw : Measure continuousPaths).map restriction).map indices.restrict)
    · exact fun _ => rfl
    · exact fun indices => (projectedSame indices).symm
  have sameContinuousMeasures : (firstContinuousLaw : Measure continuousPaths) =
      (secondContinuousLaw : Measure continuousPaths) :=
    restrictionEmbedding.map_injective sameRestrictions
  apply Subtype.ext
  calc
    (first : Measure (FiniteSupportPathSpace paths)) =
        (firstContinuousLaw : Measure continuousPaths).map Subtype.val := firstRecovered.symm
    _ = (secondContinuousLaw : Measure continuousPaths).map Subtype.val :=
      congrArg (Measure.map Subtype.val) sameContinuousMeasures
    _ = (second : Measure (FiniteSupportPathSpace paths)) := secondRecovered

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPath_law_eq_of_dense_finite_evaluations
