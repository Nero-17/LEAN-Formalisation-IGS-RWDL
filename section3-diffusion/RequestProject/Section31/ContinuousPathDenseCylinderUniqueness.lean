import RequestProject.Section31.ContinuousTimePathBorel
import RequestProject.Section31.FiniteProductFiniteMeasureUniqueness
import Mathlib.MeasureTheory.Constructions.Projective

/-! Finite continuous product cylinders on any countable dense time set
determine finite Borel measures on the entire continuous-path space. This
includes event-restricted future-path measures, whose mass need not be one.
It is a uniqueness statement, and does not presume a future Markov identity. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal BigOperators BoundedContinuousFunction
noncomputable section

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

local instance denseCylinderPathMeasurableSpace : MeasurableSpace C(ℝ≥0, State) := borel _
local instance denseCylinderPathBorelSpace : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

theorem continuousPath_finiteMeasure_eq_of_dense_product_cylinders
    (denseTimes : ℕ → ℝ≥0) (timesDense : DenseRange denseTimes)
    (first second : Measure C(ℝ≥0, State)) [IsFiniteMeasure first] [IsFiniteMeasure second]
    (sameProducts : ∀ (indices : Finset ℕ) (tests : indices → State →ᵇ ℝ),
      (∫ path, ∏ index : indices, tests index (path (denseTimes index.val)) ∂first) =
        ∫ path, ∏ index : indices, tests index (path (denseTimes index.val)) ∂second) :
    first = second := by
  have denseEmbedding := continuousMap_denseEvaluation_measurableEmbedding
    (State := State) denseTimes timesDense
  apply denseEmbedding.map_injective
  apply IsProjectiveLimit.unique
    (P := fun indices : Finset ℕ =>
      (first.map (fun path => fun index => path (denseTimes index))).map indices.restrict)
  · exact fun _ => rfl
  · intro indices
    have projectionMeasurable : Measurable (indices.restrict : (ℕ → State) → indices → State) :=
      measurable_pi_lambda _ fun index => measurable_pi_apply index.val
    dsimp only
    rw [Measure.map_map projectionMeasurable denseEmbedding.measurable,
      Measure.map_map projectionMeasurable denseEmbedding.measurable]
    symm
    apply FiniteProductWeak.finiteMeasure_eq_of_product_integrals
    intro tests
    have finiteEvaluationMeasurable : Measurable
        (fun path : C(ℝ≥0, State) => fun index : indices => path (denseTimes index.val)) :=
      (continuous_pi fun (index : indices) => continuous_eval_const (denseTimes index.val)).measurable
    have productMeasurable : Measurable
        (fun point : indices → State => ∏ index : indices, tests index (point index)) :=
      (continuous_finset_prod Finset.univ fun index _ =>
        (tests index).continuous.comp (continuous_apply index)).measurable
    change (∫ point, ∏ index : indices, tests index (point index)
        ∂first.map (fun path => fun index : indices => path (denseTimes index.val))) =
      ∫ point, ∏ index : indices, tests index (point index)
        ∂second.map (fun path => fun index : indices => path (denseTimes index.val))
    rw [integral_map finiteEvaluationMeasurable.aemeasurable productMeasurable.aestronglyMeasurable,
      integral_map finiteEvaluationMeasurable.aemeasurable productMeasurable.aestronglyMeasurable]
    exact sameProducts indices tests

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPath_finiteMeasure_eq_of_dense_product_cylinders
