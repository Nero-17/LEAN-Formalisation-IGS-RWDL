import RequestProject.Section31.SkorokhodJ1PseudoDistance
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.ContinuousOn

/-! Right continuity and genuine left limits, including the vacuous left
condition at a minimum. Uniform approximation preserves this property when
the state space is complete. The J1 subtype inherits only a pseudometric;
no separation, complete J1 metric, or Polish theorem is asserted. -/

namespace IGS.Sec31.DiscreteMarkov

open Set Filter Topology
open scoped UniformConvergence
noncomputable section

variable {Time State : Type*} [LinearOrder Time] [TopologicalSpace Time]
variable [MetricSpace State]

def IsCadlagPath (path : Time → State) : Prop :=
  (∀ time, ContinuousWithinAt path (Ici time) time) ∧
    ∀ time, ∃ value, Tendsto path (𝓝[Iio time] time) (𝓝 value)

theorem Continuous.isCadlagPath {path : Time → State} (pathContinuous : Continuous path) :
    IsCadlagPath path := by
  constructor
  · intro time
    exact pathContinuous.continuousAt.continuousWithinAt
  · intro time
    exact ⟨path time, pathContinuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩

theorem IsCadlagPath.comp_continuous_strictMono {OtherTime : Type*}
    [LinearOrder OtherTime] [TopologicalSpace OtherTime]
    {path : Time → State} (pathCadlag : IsCadlagPath path)
    (embedding : OtherTime → Time) (embeddingContinuous : Continuous embedding)
    (embeddingStrictMono : StrictMono embedding) : IsCadlagPath (path ∘ embedding) := by
  constructor
  · intro time
    exact (pathCadlag.1 (embedding time)).comp embeddingContinuous.continuousWithinAt
      (fun _ membership => embeddingStrictMono.monotone membership)
  · intro time
    obtain ⟨value, leftLimit⟩ := pathCadlag.2 (embedding time)
    refine ⟨value, leftLimit.comp ?_⟩
    exact embeddingContinuous.continuousWithinAt.tendsto_nhdsWithin
      (fun _ membership => embeddingStrictMono membership)

theorem exists_limit_of_uniform_limit_approximations [CompleteSpace State]
    (path : Time → State) (approach : Filter Time) [NeBot approach]
    (approximations : ∀ tolerance : ℝ, 0 < tolerance →
      ∃ approximation : Time → State,
        (∀ time, dist (path time) (approximation time) < tolerance) ∧
          ∃ value, Tendsto approximation approach (𝓝 value)) :
    ∃ value, Tendsto path approach (𝓝 value) := by
  apply cauchy_map_iff_exists_tendsto.mp
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance, ?_⟩
  intro tolerance tolerancePositive
  obtain ⟨approximation, uniformBound, value, approximationLimit⟩ :=
    approximations (tolerance / 4) (by linarith)
  have nearValue : ∀ᶠ time in approach, dist (approximation time) value < tolerance / 4 :=
    (Metric.tendsto_nhds.mp approximationLimit) _ (by linarith)
  refine ⟨path '' {time | dist (approximation time) value < tolerance / 4}, ?_, ?_⟩
  · change path ⁻¹' (path '' {time | dist (approximation time) value < tolerance / 4}) ∈ approach
    exact Filter.mem_of_superset nearValue (fun time bound => ⟨time, bound, rfl⟩)
  · rintro _ ⟨first, firstNear, rfl⟩ _ ⟨second, secondNear, rfl⟩
    change dist (approximation first) value < tolerance / 4 at firstNear
    change dist (approximation second) value < tolerance / 4 at secondNear
    have firstApproximation := uniformBound first
    have secondApproximation := uniformBound second
    have triangle := dist_triangle (path first) (approximation first) (path second)
    have middleTriangle := dist_triangle (approximation first) value (path second)
    have lastTriangle := dist_triangle value (approximation second) (path second)
    rw [dist_comm value (approximation second), dist_comm (approximation second) (path second)]
      at lastTriangle
    linarith

theorem isCadlagPath_of_uniform_approximations [CompleteSpace State]
    (path : Time → State)
    (approximations : ∀ tolerance : ℝ, 0 < tolerance →
      ∃ approximation : Time → State, IsCadlagPath approximation ∧
        ∀ time, dist (path time) (approximation time) < tolerance) :
    IsCadlagPath path := by
  constructor
  · intro time
    apply Metric.continuousWithinAt_iff'.mpr
    intro tolerance tolerancePositive
    obtain ⟨approximation, approximationCadlag, uniformBound⟩ :=
      approximations (tolerance / 3) (by linarith)
    have approximationNear : ∀ᶠ other in 𝓝[Ici time] time,
        dist (approximation other) (approximation time) < tolerance / 3 :=
      (Metric.continuousWithinAt_iff'.mp (approximationCadlag.1 time)) _ (by linarith)
    filter_upwards [approximationNear] with other otherNear
    have firstBound := uniformBound other
    have lastBound := uniformBound time
    have triangle := dist_triangle (path other) (approximation other) (path time)
    have secondTriangle := dist_triangle (approximation other) (approximation time) (path time)
    rw [dist_comm (approximation time) (path time)] at secondTriangle
    linarith
  · intro time
    by_cases approachNontrivial : NeBot (𝓝[Iio time] time)
    · letI cadlagLeftApproachNeBot : NeBot (𝓝[Iio time] time) := approachNontrivial
      apply exists_limit_of_uniform_limit_approximations path (𝓝[Iio time] time)
      intro tolerance tolerancePositive
      obtain ⟨approximation, approximationCadlag, uniformBound⟩ :=
        approximations tolerance tolerancePositive
      exact ⟨approximation, uniformBound, approximationCadlag.2 time⟩
    · refine ⟨path time, ?_⟩
      rw [Filter.not_neBot.mp approachNontrivial]
      exact tendsto_bot

section BoundedState
variable [BoundedSpace State] [CompleteSpace State]

theorem isClosed_uniformCadlagPaths :
    IsClosed {path : Time →ᵤ State | IsCadlagPath (UniformFun.toFun path)} := by
  apply closure_eq_iff_isClosed.mp
  apply subset_antisymm
  · intro path pathInClosure
    apply isCadlagPath_of_uniform_approximations (UniformFun.toFun path)
    intro tolerance tolerancePositive
    obtain ⟨approximation, approximationCadlag, uniformBound⟩ :=
      Metric.mem_closure_iff.mp pathInClosure tolerance tolerancePositive
    refine ⟨UniformFun.toFun approximation, approximationCadlag, ?_⟩
    intro time
    have pointBound : dist (UniformFun.toFun path time) (UniformFun.toFun approximation time) ≤
        dist path approximation :=
      (UniformFun.dist_le (dist_nonneg : 0 ≤ dist path approximation)).mp le_rfl time
    exact pointBound.trans_lt uniformBound
  · exact subset_closure

theorem uniformLimit_isCadlagPath {paths : ℕ → Time →ᵤ State} {path : Time →ᵤ State}
    (pathsCadlag : ∀ index, IsCadlagPath (UniformFun.toFun (paths index)))
    (pathsConverge : Tendsto paths atTop (𝓝 path)) :
    IsCadlagPath (UniformFun.toFun path) :=
  isClosed_uniformCadlagPaths.mem_of_tendsto pathsConverge (Filter.Eventually.of_forall pathsCadlag)

end BoundedState

/-- The genuine right-continuous, left-limit subtype, carrying the stated
time-change pseudometric inherited from J1Function. -/
def CadlagJ1Path (Time State : Type*) [LinearOrder Time] [TopologicalSpace Time]
    [MetricSpace State] : Type _ :=
  {path : J1Function Time State // IsCadlagPath path.toFun}

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.isClosed_uniformCadlagPaths
#print axioms IGS.Sec31.DiscreteMarkov.uniformLimit_isCadlagPath
