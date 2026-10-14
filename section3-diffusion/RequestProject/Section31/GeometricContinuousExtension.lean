import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-! Construct a bounded continuous extension from summable uniform increments
of continuous approximants. Eventual agreement on the skeleton identifies the
extension, without assuming that the original skeleton function is continuous.
Actual harmonic increment bounds are supplied separately. -/

namespace IGS.Sec31

open Filter Topology
noncomputable section
variable {Space Vertex : Type*} [TopologicalSpace Space]

theorem exists_continuous_extension_of_geometric_uniform_increments
    (embedding : Vertex → Space) (values : Vertex → ℝ)
    (approximation : ℕ → Space →ᵇ ℝ)
    (constant factor : ℝ) (factorNonnegative : 0 ≤ factor) (factorStrict : factor < 1)
    (increments : ∀ level, ‖approximation (level + 1) - approximation level‖ ≤ constant * factor ^ level)
    (agreement : ∀ vertex, ∀ᶠ level in atTop, approximation level (embedding vertex) = values vertex) :
    ∃ extension : Space →ᵇ ℝ,
      Tendsto approximation atTop (𝓝 extension) ∧
      ∀ vertex, extension (embedding vertex) = values vertex := by
  have distances : ∀ level,
      dist (approximation level) (approximation (level + 1)) ≤ constant * factor ^ level := by
    intro level
    rw [dist_eq_norm, norm_sub_rev]
    exact increments level
  have summable : Summable (fun level : ℕ => constant * factor ^ level) :=
    (summable_geometric_of_lt_one factorNonnegative factorStrict).mul_left constant
  obtain ⟨extension, convergence⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable _ distances summable)
  refine ⟨extension, convergence, ?_⟩
  intro vertex
  have pointConvergence : Tendsto (fun level => approximation level (embedding vertex))
      atTop (𝓝 (extension (embedding vertex))) :=
    (continuous_eval_const (embedding vertex)).continuousAt.tendsto.comp convergence
  exact tendsto_nhds_unique pointConvergence (tendsto_const_nhds.congr' (agreement vertex).symm)

end
end IGS.Sec31

#print axioms IGS.Sec31.exists_continuous_extension_of_geometric_uniform_increments
