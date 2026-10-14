import RequestProject.Section31.EIGSMovingStartApproximation
import RequestProject.Section31.EIGSNativeSupSemigroupConvergence
import RequestProject.Section31.BanachBackwardObservations

/-! The actual all-vertex supremum limit determines a continuous semigroup
uniquely. Every completion point is approached by vertices at every level,
so two such limits give two limits of the same scalar evaluations. -/

namespace EIGS

open IGS.Sec31 Filter Topology
open scoped NNReal
noncomputable section

variable {K : ℕ}

theorem xiNativeSupSemigroup_limit_unique (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected) [CompactSpace parameters.LimitSpace]
    (resistanceRate normalization : ℝ)
    (firstSemigroup secondSemigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ))
    (firstLimit : ∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
      Tendsto (fun level => ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time
        (fun vertex => function (parameters.vertexEmbedding level vertex)) -
        (fun vertex => firstSemigroup time function (parameters.vertexEmbedding level vertex))‖) atTop (𝓝 0))
    (secondLimit : ∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
      Tendsto (fun level => ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time
        (fun vertex => function (parameters.vertexEmbedding level vertex)) -
        (fun vertex => secondSemigroup time function (parameters.vertexEmbedding level vertex))‖) atTop (𝓝 0)) :
    firstSemigroup = secondSemigroup := by
  funext time
  apply ContinuousLinearMap.ext
  intro function
  apply ContinuousMap.ext
  intro point
  obtain ⟨starts, startsConverge⟩ := parameters.exists_moving_starts point
  have firstScalar := BanachBackwardObservations.moving_start_evaluation_limit
    parameters.vertexEmbedding
    (fun level => xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time
      (fun vertex => function (parameters.vertexEmbedding level vertex)))
    (firstSemigroup time function) (firstLimit time function) starts point startsConverge
  have secondScalar := BanachBackwardObservations.moving_start_evaluation_limit
    parameters.vertexEmbedding
    (fun level => xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time
      (fun vertex => function (parameters.vertexEmbedding level vertex)))
    (secondSemigroup time function) (secondLimit time function) starts point startsConverge
  exact tendsto_nhds_unique firstScalar secondScalar

end
end EIGS

#print axioms EIGS.xiNativeSupSemigroup_limit_unique
