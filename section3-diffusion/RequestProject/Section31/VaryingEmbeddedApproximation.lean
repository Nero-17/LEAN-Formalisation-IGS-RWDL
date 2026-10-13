import RequestProject.Section31.VaryingEmbeddedL2Core
import RequestProject.Section31.VaryingL2Approximation

/-! Uniform core convergence gives Strong convergence in the original level L² spaces. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]
  {LevelSpace : ℕ → Type*} [∀ level, MeasurableSpace (LevelSpace level)]

theorem embedded_uniformly_convergent_functions_L2_strong
    (measures : ∀ level, ProbabilityMeasure (LevelSpace level))
    (embeddings : ∀ level, LevelSpace level → Space)
    (measurable_embeddings : ∀ level, Measurable (embeddings level))
    (measure : ProbabilityMeasure Space)
    (weak_convergence : Tendsto
      (embeddedProbabilityMeasures measures embeddings measurable_embeddings) atTop (𝓝 measure))
    (functions : ℕ → Space →ᵇ ℝ) (function : Space →ᵇ ℝ)
    (uniform_convergence : Tendsto functions atTop (𝓝 function)) :
    (embeddedProbabilityL2Core measures embeddings measurable_embeddings measure weak_convergence).Strong
      (fun level =>
        (embeddedProbabilityL2Core measures embeddings measurable_embeddings measure weak_convergence).restrict
          level (functions level))
      (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ function) := by
  let core := embeddedProbabilityL2Core measures embeddings measurable_embeddings measure weak_convergence
  apply core.strong_of_norm_sub_tendsto_zero _ (fun level => core.restrict level function)
    _ (core.strong_restrict function)
  have sup_error : Tendsto (fun level => ‖functions level - function‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (uniform_convergence.sub (tendsto_const_nhds (x := function))).norm
  apply squeeze_zero (fun _ => norm_nonneg _) _ sup_error
  intro level
  rw [← map_sub]
  change ‖(Lp.compMeasurePreservingₗᵢ ℝ (embeddings level)
    (embeddingMeasurePreserving measures embeddings measurable_embeddings level))
      (BoundedContinuousFunction.toLp 2
        (embeddedProbabilityMeasures measures embeddings measurable_embeddings level : Measure Space)
        ℝ (functions level - function))‖ ≤ ‖functions level - function‖
  rw [LinearIsometry.norm_map]
  exact boundedContinuous_L2_norm_le_sup
    (embeddedProbabilityMeasures measures embeddings measurable_embeddings level) (functions level - function)

end IGS.Sec31
