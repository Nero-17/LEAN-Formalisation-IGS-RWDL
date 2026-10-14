import RequestProject.Section31.CountableMetricRealisation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.SpecificLimits.Basic

/-! The finite projection version of the countable ambient construction.
The source metrics and the target metric are the metrics supplied by the
caller; in particular diameter-normalized metrics can be supplied unchanged.
No equality with any native path-space metric is presumed.

The projection-distortion formulation was suggested by
IGSIII34/Topology/CommonProjectionMetricRealisationCompletion.lean, reference
commit cb0183af15f571bb0b1b5d3b8de367a419716f1b. This independent RWDL proof
uses its own preceding countable amalgamation and Lean 4.28 mathlib gluing. -/

namespace EIGS.CountableRealisation
noncomputable section
open Metric Set Filter
open scoped Topology
universe u

theorem exists_compact_common_realisation_of_projection_distortion
    (Sources : ℕ → Type u) [∀ n, MetricSpace (Sources n)]
    [∀ n, Fintype (Sources n)] [∀ n, Nonempty (Sources n)]
    {Target : Type u} [MetricSpace Target] [CompactSpace Target] [Nonempty Target]
    (projection : ∀ n, Sources n → Target)
    (distortionZero : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n in atTop,
      ∀ first second : Sources n,
        |dist first second - dist (projection n first) (projection n second)| < epsilon) :
    ∃ (Ambient : Type u) (ambientMetric : MetricSpace Ambient),
      letI := ambientMetric
      CompleteSpace Ambient ∧ CompactSpace Ambient ∧
      ∃ target : Target → Ambient, Isometry target ∧
      ∃ sources : ∀ n, Sources n → Ambient,
        (∀ n, Isometry (sources n)) ∧
        ∃ radii : ℕ → ℝ, (∀ n, 0 < radii n) ∧ Tendsto radii atTop (𝓝 0) ∧
          (∀ n point, dist (sources n point) (target (projection n point)) = radii n) ∧
          ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n in atTop,
            ∀ point, dist (sources n point) (target (projection n point)) < epsilon := by
  classical
  let errors : ℕ → ℝ := fun n => Finset.univ.sup' Finset.univ_nonempty
    (fun pair : Sources n × Sources n =>
      |dist pair.1 pair.2 - dist (projection n pair.1) (projection n pair.2)|)
  have errorsNonnegative (n : ℕ) : 0 ≤ errors n := by
    let point : Sources n := Classical.choice inferInstance
    exact (abs_nonneg (dist point point - dist (projection n point) (projection n point))).trans
      (Finset.le_sup' (f := fun pair : Sources n × Sources n =>
        |dist pair.1 pair.2 - dist (projection n pair.1) (projection n pair.2)|)
        (Finset.mem_univ (point, point)))
  have errorBound (n : ℕ) (first second : Sources n) :
      |dist first second - dist (projection n first) (projection n second)| ≤ errors n :=
    Finset.le_sup' (f := fun pair : Sources n × Sources n =>
      |dist pair.1 pair.2 - dist (projection n pair.1) (projection n pair.2)|)
      (Finset.mem_univ (first, second))
  have errorsZero : Tendsto errors atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro epsilon positive
    filter_upwards [distortionZero epsilon positive] with n small
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (errorsNonnegative n)]
    exact (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun pair _ => small pair.1 pair.2)
  let radii : ℕ → ℝ := fun n => errors n + (n + 1 : ℝ)⁻¹
  have radiiPositive (n : ℕ) : 0 < radii n := by
    have nonnegative := errorsNonnegative n
    dsimp only [radii]
    positivity
  have radiiZero : Tendsto radii atTop (𝓝 0) := by
    have inversesZero : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa only [add_zero] using errorsZero.add inversesZero
  let Extensions : ℕ → Type u := fun n => Sources n ⊕ Target
  let extensionMetrics : ∀ n, MetricSpace (Extensions n) := fun n =>
    glueMetricApprox (id : Sources n → Sources n) (projection n) (radii n) (radiiPositive n)
      (fun first second => (errorBound n first second).trans (by
        have nonnegative := errorsNonnegative n
        have inverseNonnegative : 0 ≤ (n + 1 : ℝ)⁻¹ := by positivity
        dsimp only [radii]
        linarith))
  letI finiteProjectionExtensionMetric : ∀ n, MetricSpace (Extensions n) := extensionMetrics
  let roots : ∀ n, Target → Extensions n := fun _ => Sum.inr
  have rootIsometry (n : ℕ) : Isometry (roots n) := Isometry.of_dist_eq (fun _ _ => rfl)
  have sourceIsometry (n : ℕ) : Isometry (@Sum.inl (Sources n) Target) :=
    Isometry.of_dist_eq (fun _ _ => rfl)
  have bridge (n : ℕ) (point : Sources n) :
      dist (Sum.inl point : Extensions n) (roots n (projection n point)) = radii n :=
    glueDist_glued_points id (projection n) (radii n) point
  letI finiteProjectionExtensionCompact : ∀ n, CompactSpace (Extensions n) := fun n => by
    have compact := (isCompact_range (sourceIsometry n).continuous).union
      (isCompact_range (rootIsometry n).continuous)
    have cover : range (@Sum.inl (Sources n) Target) ∪ range (roots n) = univ := by
      ext point
      cases point <;> simp [roots]
    rw [cover] at compact
    exact isCompact_univ_iff.mp compact
  have extensionClose (n : ℕ) (point : Extensions n) :
      ∃ base, dist point (roots n base) ≤ radii n := by
    cases point with
    | inl point => exact ⟨projection n point, (bridge n point).le⟩
    | inr point => exact ⟨point, by simpa [roots] using (radiiPositive n).le⟩
  letI finiteProjectionAmbientCompact : CompactSpace (CompleteAmalgamation Extensions roots rootIsometry) :=
    completeAmalgamation_compact Extensions roots rootIsometry radii radiiZero extensionClose
  let target := rootInAmbient Extensions roots rootIsometry
  let sources : ∀ n, Sources n → CompleteAmalgamation Extensions roots rootIsometry :=
    fun n => extensionInAmbient Extensions roots rootIsometry n ∘ Sum.inl
  have projectedDistance (n : ℕ) (point : Sources n) :
      dist (sources n point) (target (projection n point)) = radii n :=
    (extension_root_distance Extensions roots rootIsometry n (Sum.inl point) (projection n point)).trans
      (bridge n point)
  refine ⟨CompleteAmalgamation Extensions roots rootIsometry, inferInstance,
    inferInstance, inferInstance, target, rootInAmbient_isometry Extensions roots rootIsometry,
    sources, fun n => (extensionInAmbient_isometry Extensions roots rootIsometry n).comp (sourceIsometry n),
    radii, radiiPositive, radiiZero, projectedDistance, ?_⟩
  intro epsilon positive
  filter_upwards [radiiZero.eventually (gt_mem_nhds positive)] with n small
  intro point
  exact (projectedDistance n point).trans_lt small

end
end EIGS.CountableRealisation

#print axioms EIGS.CountableRealisation.exists_compact_common_realisation_of_projection_distortion
