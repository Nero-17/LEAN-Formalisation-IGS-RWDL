import RequestProject.Section31.ContinuousTimePathBorel

/-! Random nonnegative time translation of a continuous path. The source
measurable space may be larger than the Borel sigma-field (for example a
completion); the target is explicitly the ordinary continuous-path Borel
space. Measurability is proved through the existing dense evaluations. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal
noncomputable section

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]

def continuousPathRandomShift (time : C(ℝ≥0, State) → ℝ≥0)
    (path : C(ℝ≥0, State)) : C(ℝ≥0, State) :=
  ⟨fun delay => path (time path + delay),
    path.continuous.comp (continuous_const.add continuous_id)⟩

@[simp] theorem continuousPathRandomShift_apply (time : C(ℝ≥0, State) → ℝ≥0)
    (path : C(ℝ≥0, State)) (delay : ℝ≥0) :
    continuousPathRandomShift time path delay = path (time path + delay) := rfl

theorem continuousPathRandomShift_measurable
    [ambient : MeasurableSpace C(ℝ≥0, State)] [OpensMeasurableSpace C(ℝ≥0, State)]
    (time : C(ℝ≥0, State) → ℝ≥0) (timeMeasurable : Measurable time) :
    @Measurable C(ℝ≥0, State) C(ℝ≥0, State) ambient (borel C(ℝ≥0, State))
      (continuousPathRandomShift time) := by
  have denseEmbedding := continuousMap_denseEvaluation_measurableEmbedding
    (State := State) (TopologicalSpace.denseSeq ℝ≥0)
    (TopologicalSpace.denseRange_denseSeq ℝ≥0)
  have coordinatesMeasurable : @Measurable C(ℝ≥0, State) (ℕ → State) ambient inferInstance
      ((fun path : C(ℝ≥0, State) => fun index => path (TopologicalSpace.denseSeq ℝ≥0 index)) ∘
        continuousPathRandomShift time) := by
    apply measurable_pi_lambda
    intro index
    exact continuous_eval.measurable.comp
      (measurable_id.prodMk (timeMeasurable.add_const (TopologicalSpace.denseSeq ℝ≥0 index)))
  exact (@MeasurableEmbedding.measurable_comp_iff C(ℝ≥0, State) C(ℝ≥0, State) (ℕ → State)
    ambient (borel C(ℝ≥0, State)) inferInstance (continuousPathRandomShift time)
    (fun path : C(ℝ≥0, State) => fun index => path (TopologicalSpace.denseSeq ℝ≥0 index))
    denseEmbedding).mp coordinatesMeasurable

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPathRandomShift_measurable
