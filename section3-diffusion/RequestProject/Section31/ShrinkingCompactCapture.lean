import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-! A compactness lemma for transferring tightness in an ambient metric
space that need not be complete. The limiting compact set is explicitly
included, so no completion points are silently added. -/

namespace IGS.Sec31.DiscreteMarkov
noncomputable section
open Set Filter
open scoped Topology

theorem shrinking_compact_capture_union_isCompact
    {Space : Type*} [MetricSpace Space]
    (limitSet : Set Space) (limitCompact : IsCompact limitSet)
    (captures : ℕ → Set Space) (captureCompact : ∀ index, IsCompact (captures index))
    (errors : ℕ → ℝ) (errorsNonnegative : ∀ index, 0 ≤ errors index)
    (errorsVanish : Tendsto errors atTop (𝓝 0))
    (near : ∀ index, ∀ point ∈ captures index,
      ∃ limitPoint ∈ limitSet, dist point limitPoint ≤ errors index) :
    IsCompact (limitSet ∪ ⋃ index, captures index) := by
  classical
  apply IsSeqCompact.isCompact
  intro sequence membership
  by_cases boundedFrequently : ∃ cap : ℕ,
      ∃ᶠ index in atTop, sequence index ∈ limitSet ∪ accumulate captures cap
  · obtain ⟨cap, frequent⟩ := boundedFrequently
    obtain ⟨point, pointIn, subsequence, increasing, converges⟩ :=
      (limitCompact.union (isCompact_accumulate captureCompact cap)).tendsto_subseq' frequent
    refine ⟨point, ?_, subsequence, increasing, converges⟩
    rcases pointIn with pointIn | pointIn
    · exact Or.inl pointIn
    · exact Or.inr ((accumulate_subset_iUnion cap) pointIn)
  · have witnesses : ∀ index, ∃ captureIndex : ℕ, ∃ limitPoint ∈ limitSet,
        dist (sequence index) limitPoint ≤ errors captureIndex ∧
          (sequence index ∈ limitSet ∨ sequence index ∈ captures captureIndex) := by
      intro index
      rcases membership index with inLimit | inCapture
      · exact ⟨0, sequence index, inLimit, by simpa using errorsNonnegative 0, Or.inl inLimit⟩
      · obtain ⟨captureIndex, inCapture⟩ := mem_iUnion.mp inCapture
        obtain ⟨limitPoint, inLimit, close⟩ := near captureIndex _ inCapture
        exact ⟨captureIndex, limitPoint, inLimit, close, Or.inr inCapture⟩
    choose captureIndex limitPoint limitMembership distanceBound captureMembership using witnesses
    have indicesDiverge : Tendsto captureIndex atTop atTop := by
      apply tendsto_atTop.mpr
      intro cap
      have outside : ∀ᶠ index in atTop,
          sequence index ∉ limitSet ∪ accumulate captures cap := by
        exact not_frequently.mp (fun frequent => boundedFrequently ⟨cap, frequent⟩)
      filter_upwards [outside] with index outside
      by_contra below
      rcases captureMembership index with inLimit | inCapture
      · exact outside (Or.inl inLimit)
      · apply outside
        right
        exact mem_biUnion (Nat.le_of_lt (Nat.lt_of_not_ge below)) inCapture
    have distanceVanishes : Tendsto (fun index => dist (sequence index) (limitPoint index)) atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg) distanceBound (errorsVanish.comp indicesDiverge)
    obtain ⟨point, pointIn, subsequence, increasing, converges⟩ := limitCompact.tendsto_subseq limitMembership
    refine ⟨point, Or.inl pointIn, subsequence, increasing, ?_⟩
    exact (tendsto_iff_of_dist (distanceVanishes.comp increasing.tendsto_atTop)).mpr converges

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.shrinking_compact_capture_union_isCompact
