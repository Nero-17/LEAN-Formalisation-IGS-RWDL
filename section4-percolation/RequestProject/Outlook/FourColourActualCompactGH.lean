import RequestProject.Outlook.FourColourActualCompletion
import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Analysis.SpecificLimits.Basic

/-! Compactness and quantitative GH convergence of actual normalized source components.
The only input is the actual Conf/coarse-compatible family, not a compactness/net premise.
This is pathwise metric geometry; probability and vertex/speed measures are not identified. -/
noncomputable section
namespace Outlook.FourColourActualCompactGH
open Cluster Outlook.FourColourActualMesh Outlook.FourColourActualCompletion
open Set Filter Topology Metric

instance stageNonempty (family : CompatibleConfigurations) (depth : ℕ) :
    Nonempty (Stage family depth) := ⟨stageSource family depth⟩

def stageAdvance (family : CompatibleConfigurations) (first last : ℕ) (lowerBound : first ≤ last)
    (vertex : Stage family first) : Stage family last :=
  Nat.leRecOn lowerBound (nextStage family _) vertex

theorem toCompletion_stageAdvance (family : CompatibleConfigurations) (first last : ℕ)
    (lowerBound : first ≤ last) (vertex : Stage family first) :
    toCompletion family last (stageAdvance family first last lowerBound vertex) = toCompletion family first vertex := by
  induction last, lowerBound using Nat.le_induction with
  | base => simp only [stageAdvance, Nat.leRecOn_self]
  | succ last lowerBound induction =>
      rw [stageAdvance, Nat.leRecOn_succ lowerBound, toCompletion_commute]
      simpa only [stageAdvance] using induction

/-- A finite union of genuine level-centered closed balls. -/
def stageCover (family : CompatibleConfigurations) (depth : ℕ) : Set (SourceCompletion family) :=
  ⋃ vertex : Stage family depth, closedBall (toCompletion family depth vertex) (distanceScale depth)

theorem stageCover_closed (family : CompatibleConfigurations) (depth : ℕ) :
    IsClosed (stageCover family depth) :=
  isClosed_iUnion_of_finite (fun _ => isClosed_closedBall)

theorem stages_subset_stageCover (family : CompatibleConfigurations) (depth : ℕ) :
    (⋃ highest, range (toCompletion family highest)) ⊆ stageCover family depth := by
  intro point membership
  rcases mem_iUnion.mp membership with ⟨highest, vertex, rfl⟩
  by_cases lowerBound : depth ≤ highest
  · obtain ⟨original, bound⟩ := completion_finite_tail family highest depth lowerBound vertex
    apply mem_iUnion.mpr
    refine ⟨original, Metric.mem_closedBall.mpr ?_⟩
    exact le_trans bound (sub_le_self _ (le_of_lt (distanceScale_pos highest)))
  · have earlier : highest ≤ depth := by omega
    apply mem_iUnion.mpr
    refine ⟨stageAdvance family highest depth earlier vertex, Metric.mem_closedBall.mpr ?_⟩
    rw [toCompletion_stageAdvance, dist_self]
    exact le_of_lt (distanceScale_pos depth)

/-- The actual finite level is a closed-radius net for every point of the completion. -/
theorem completion_mesh (family : CompatibleConfigurations) (depth : ℕ)
    (point : SourceCompletion family) :
    ∃ original : Stage family depth,
      dist point (toCompletion family depth original) ≤ distanceScale depth := by
  have coverAll : (univ : Set (SourceCompletion family)) ⊆ stageCover family depth := by
    rw [← (stages_dense_in_completion family).closure_eq]
    exact (stageCover_closed family depth).closure_subset_iff.mpr (stages_subset_stageCover family depth)
  have membership := coverAll (mem_univ point)
  rcases mem_iUnion.mp membership with ⟨original, bound⟩
  exact ⟨original, Metric.mem_closedBall.mp bound⟩

theorem completion_finite_net (family : CompatibleConfigurations) (depth : ℕ) :
    (range (toCompletion family depth)).Finite ∧
      ∀ point : SourceCompletion family, ∃ center ∈ range (toCompletion family depth),
        dist point center ≤ distanceScale depth := by
  refine ⟨finite_range _, ?_⟩
  intro point
  obtain ⟨original, bound⟩ := completion_mesh family depth point
  exact ⟨toCompletion family depth original, ⟨original, rfl⟩, bound⟩

theorem distanceScale_tendsto_zero : Tendsto distanceScale atTop (𝓝 (0 : ℝ)) := by
  have limit : Tendsto (fun depth : ℕ => ((2 : ℝ)⁻¹) ^ depth) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [distanceScale, inv_pow] using limit

/-- Total boundedness is proved from the actual finite source levels. -/
theorem completion_totallyBounded (family : CompatibleConfigurations) :
    TotallyBounded (univ : Set (SourceCompletion family)) := by
  apply Metric.totallyBounded_iff.mpr
  intro radius positiveRadius
  have eventuallySmall : ∀ᶠ depth in atTop, distanceScale depth < radius :=
    distanceScale_tendsto_zero.eventually (gt_mem_nhds positiveRadius)
  obtain ⟨depth, small⟩ := eventuallySmall.exists
  refine ⟨range (toCompletion family depth), finite_range _, ?_⟩
  intro point membership
  obtain ⟨original, bound⟩ := completion_mesh family depth point
  apply mem_iUnion.mpr
  refine ⟨toCompletion family depth original, mem_iUnion.mpr ?_⟩
  exact ⟨⟨original, rfl⟩, Metric.mem_ball.mpr (lt_of_le_of_lt bound small)⟩

/-- The actual compatible completion is compact, with no compactness hypothesis. -/
instance completionCompactSpace (family : CompatibleConfigurations) :
    CompactSpace (SourceCompletion family) :=
  ⟨(completion_totallyBounded family).isCompact_of_isClosed isClosed_univ⟩

theorem completion_hausdorff_bound (family : CompatibleConfigurations) (depth : ℕ) :
    hausdorffDist (range (toCompletion family depth)) (univ : Set (SourceCompletion family)) ≤ distanceScale depth := by
  apply hausdorffDist_le_of_mem_dist (le_of_lt (distanceScale_pos depth))
  · intro point membership
    exact ⟨point, mem_univ point, by simpa only [dist_self] using le_of_lt (distanceScale_pos depth)⟩
  · intro point membership
    obtain ⟨original, bound⟩ := completion_mesh family depth point
    exact ⟨toCompletion family depth original, ⟨original, rfl⟩, bound⟩

/-- The actual finite-source metric is within2^(-depth) of its compact completion in GH distance. -/
theorem completion_gh_bound (family : CompatibleConfigurations) (depth : ℕ) :
    GromovHausdorff.ghDist (Stage family depth) (SourceCompletion family) ≤ distanceScale depth := by
  calc
    _ ≤ hausdorffDist (range (toCompletion family depth))
        (range (id : SourceCompletion family → SourceCompletion family)) :=
      GromovHausdorff.ghDist_le_hausdorffDist (toCompletion_isometry family depth) isometry_id
    _ = hausdorffDist (range (toCompletion family depth)) (univ : Set (SourceCompletion family)) := by
      rw [range_id]
    _ ≤ distanceScale depth := completion_hausdorff_bound family depth

theorem completion_gh_tendsto_zero (family : CompatibleConfigurations) :
    Tendsto (fun depth => GromovHausdorff.ghDist (Stage family depth) (SourceCompletion family)) atTop (𝓝 0) := by
  apply squeeze_zero ?_ (completion_gh_bound family) distanceScale_tendsto_zero
  intro depth
  unfold GromovHausdorff.ghDist
  exact dist_nonneg

end Outlook.FourColourActualCompactGH

#print axioms Outlook.FourColourActualCompactGH.completion_mesh
#print axioms Outlook.FourColourActualCompactGH.completion_finite_net
#print axioms Outlook.FourColourActualCompactGH.completion_totallyBounded
#print axioms Outlook.FourColourActualCompactGH.completionCompactSpace
#print axioms Outlook.FourColourActualCompactGH.completion_gh_bound
#print axioms Outlook.FourColourActualCompactGH.completion_gh_tendsto_zero
