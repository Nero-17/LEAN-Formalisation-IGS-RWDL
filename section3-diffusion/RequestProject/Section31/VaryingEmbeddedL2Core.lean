import RequestProject.Section31.VaryingL2Core

/-! The continuous core directly on the level spaces' own L² spaces.

Level vertex types need not be identified with the common space. Measurable
embeddings push their probability speed measures forward; pullback of actual
Lp classes is a linear isometry. Thus weak convergence of the pushed-forward
measures supplies the core on the original level L² spaces themselves.
-/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]
  {LevelSpace : ℕ → Type*} [∀ level, MeasurableSpace (LevelSpace level)]

noncomputable def embeddedProbabilityMeasures
    (measures : ∀ level, ProbabilityMeasure (LevelSpace level))
    (embeddings : ∀ level, LevelSpace level → Space)
    (measurable_embeddings : ∀ level, Measurable (embeddings level)) : ℕ → ProbabilityMeasure Space :=
  fun level => (measures level).map (measurable_embeddings level).aemeasurable

def embeddingMeasurePreserving
    (measures : ∀ level, ProbabilityMeasure (LevelSpace level))
    (embeddings : ∀ level, LevelSpace level → Space)
    (measurable_embeddings : ∀ level, Measurable (embeddings level)) (level : ℕ) :
    MeasurePreserving (embeddings level) (measures level : Measure (LevelSpace level))
      (embeddedProbabilityMeasures measures embeddings measurable_embeddings level : Measure Space) :=
  ⟨measurable_embeddings level, rfl⟩

noncomputable def embeddedProbabilityL2Core
    (measures : ∀ level, ProbabilityMeasure (LevelSpace level))
    (embeddings : ∀ level, LevelSpace level → Space)
    (measurable_embeddings : ∀ level, Measurable (embeddings level))
    (measure : ProbabilityMeasure Space)
    (weak_convergence : Tendsto
      (embeddedProbabilityMeasures measures embeddings measurable_embeddings) atTop (𝓝 measure)) :
    VaryingHilbertCore (Space →ᵇ ℝ) (Lp ℝ 2 (measure : Measure Space))
      (fun level => Lp ℝ 2 (measures level : Measure (LevelSpace level))) where
  embed := (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ).toLinearMap
  restrict := fun level =>
    (Lp.compMeasurePreservingₗᵢ ℝ (embeddings level)
      (embeddingMeasurePreserving measures embeddings measurable_embeddings level)).toLinearMap.comp
        (BoundedContinuousFunction.toLp 2
          (embeddedProbabilityMeasures measures embeddings measurable_embeddings level : Measure Space) ℝ).toLinearMap
  dense := BoundedContinuousFunction.toLp_denseRange ℝ (measure : Measure Space) ℝ (by norm_num)
  norm_converges := by
    intro function
    have convergence := boundedContinuous_L2_norm_tendsto
      (embeddedProbabilityMeasures measures embeddings measurable_embeddings) measure weak_convergence function
    convert convergence using 1
    funext level
    exact (Lp.compMeasurePreservingₗᵢ ℝ (embeddings level)
      (embeddingMeasurePreserving measures embeddings measurable_embeddings level)).norm_map _

end IGS.Sec31
