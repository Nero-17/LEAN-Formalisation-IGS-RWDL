import RequestProject.Outlook.FourColourActualLengthInterface

/-! Genuine two-step walk compression and exact old-vertex graph distances.
The actual statements consume the already-proved concrete incidence interface;
no compression or isometry conclusion is assumed. -/
namespace Cluster.TTN.ReflectsTwoSteps
open Cluster.TTN

/-- Arbitrary fine endpoints carry explicit old preimages throughout the length induction. -/
private theorem compress_by_length {coarseNetwork fineNetwork : TTN}
    {embedding : TerminalEmbedding coarseNetwork fineNetwork}
    (partition : OldNewPartition embedding) (reflection : ReflectsTwoSteps embedding) :
    ∀ length : ℕ, ∀ (fineFirst fineLast : fineNetwork.V)
      (walk : fineNetwork.underlyingGraph.Walk fineFirst fineLast), walk.length = length →
      ∀ (first last : coarseNetwork.V), embedding.vertices first = fineFirst →
        embedding.vertices last = fineLast →
        ∃ compressed : coarseNetwork.underlyingGraph.Walk first last,
          2 * compressed.length ≤ walk.length := by
  intro length
  induction length using Nat.strong_induction_on with
  | h length induction =>
      intro fineFirst fineLast walk lengthEqual first last firstEqual lastEqual
      cases walk with
      | nil =>
          have equal : first = last := embedding.vertices.injective (firstEqual.trans lastEqual.symm)
          subst last
          exact ⟨.nil, by simp only [SimpleGraph.Walk.length_nil, Nat.mul_zero, le_refl]⟩
      | @cons fineFirst middle fineLast firstAdjacent rest =>
          have firstOld : partition.old fineFirst = true := by
            rw [← firstEqual]
            exact (partition.old_iff _).mpr ⟨first, rfl⟩
          cases rest with
          | nil =>
              have lastOld : partition.old fineLast = true := by
                rw [← lastEqual]
                exact (partition.old_iff _).mpr ⟨last, rfl⟩
              exact (partition.adjacent_alternates firstAdjacent (firstOld.trans lastOld.symm)).elim
          | @cons middle next fineLast secondAdjacent remainder =>
              have firstDifferent := partition.adjacent_alternates firstAdjacent
              have secondDifferent := partition.adjacent_alternates secondAdjacent
              have nextOld : partition.old next = true := by
                rw [firstOld] at firstDifferent
                cases middleValue : partition.old middle <;>
                  cases nextValue : partition.old next <;> simp_all
              obtain ⟨nextCoarse, nextEqual⟩ := (partition.old_iff next).mp nextOld
              have shorter : remainder.length < length := by
                simp only [SimpleGraph.Walk.length_cons] at lengthEqual
                omega
              obtain ⟨compressed, lengthBound⟩ :=
                induction remainder.length shorter next fineLast remainder rfl nextCoarse last nextEqual lastEqual
              have firstStep : fineNetwork.underlyingGraph.Adj (embedding.vertices first) middle := by
                rw [firstEqual]
                exact firstAdjacent
              have secondStep : fineNetwork.underlyingGraph.Adj middle (embedding.vertices nextCoarse) := by
                rw [nextEqual]
                exact secondAdjacent
              rcases reflection first nextCoarse middle firstStep secondStep with returnToFirst | coarseAdjacent
              · subst nextCoarse
                refine ⟨compressed, ?_⟩
                simp only [SimpleGraph.Walk.length_cons]
                omega
              · refine ⟨.cons coarseAdjacent compressed, ?_⟩
                simp only [SimpleGraph.Walk.length_cons]
                omega

/-- Delete two-step returns and compress each genuine crossing to one coarse edge. -/
theorem compress_walk {coarseNetwork fineNetwork : TTN}
    {embedding : TerminalEmbedding coarseNetwork fineNetwork}
    (partition : OldNewPartition embedding) (reflection : ReflectsTwoSteps embedding)
    {first last : coarseNetwork.V}
    (walk : fineNetwork.underlyingGraph.Walk (embedding.vertices first) (embedding.vertices last)) :
    ∃ compressed : coarseNetwork.underlyingGraph.Walk first last,
      2 * compressed.length ≤ walk.length :=
  compress_by_length partition reflection walk.length _ _ walk rfl first last rfl rfl

end Cluster.TTN.ReflectsTwoSteps

namespace Outlook.FourColourActualMetric
open Cluster Outlook.FourColourActualCoarseEmbedding Outlook.FourColourActualCoarseRetraction
open Outlook.FourColourActualLengthInterface

theorem actual_walk_compression (depth : ℕ) (configuration : Conf (depth + 1))
    {first last : (net depth (coarse depth configuration)).V}
    (walk : (net (depth + 1) configuration).underlyingGraph.Walk
      ((actualOldEmbedding depth configuration).vertices first)
      ((actualOldEmbedding depth configuration).vertices last)) :
    ∃ compressed : (net depth (coarse depth configuration)).underlyingGraph.Walk first last,
      2 * compressed.length ≤ walk.length :=
  TTN.ReflectsTwoSteps.compress_walk (actualPartition depth configuration)
    (actual_two_step_reflection depth configuration) walk

/-- The reverse extended-distance inequality is derived from real walk compression. -/
theorem actual_twice_edist_le (depth : ℕ) (configuration : Conf (depth + 1))
    (first last : (net depth (coarse depth configuration)).V) :
    2 * (net depth (coarse depth configuration)).underlyingGraph.edist first last ≤
      (net (depth + 1) configuration).underlyingGraph.edist
        ((actualOldEmbedding depth configuration).vertices first)
        ((actualOldEmbedding depth configuration).vertices last) := by
  by_cases reachable : (net (depth + 1) configuration).underlyingGraph.Reachable
      ((actualOldEmbedding depth configuration).vertices first)
      ((actualOldEmbedding depth configuration).vertices last)
  · obtain ⟨walk, shortest⟩ := reachable.exists_walk_length_eq_edist
    obtain ⟨compressed, lengthBound⟩ := actual_walk_compression depth configuration walk
    calc
      2 * (net depth (coarse depth configuration)).underlyingGraph.edist first last
          ≤ 2 * (compressed.length : ℕ∞) := mul_le_mul_left' compressed.edist_le 2
      _ = ((2 * compressed.length : ℕ) : ℕ∞) := (ENat.coe_mul 2 compressed.length).symm
      _ ≤ (walk.length : ℕ∞) := ENat.coe_le_coe.mpr lengthBound
      _ = (net (depth + 1) configuration).underlyingGraph.edist
          ((actualOldEmbedding depth configuration).vertices first)
          ((actualOldEmbedding depth configuration).vertices last) := shortest
  · rw [SimpleGraph.edist_eq_top_of_not_reachable reachable]
    exact le_top

/-- Exact doubling also covers disconnected pairs, whose distances are infinity. -/
theorem actual_old_edist_eq_twice (depth : ℕ) (configuration : Conf (depth + 1))
    (first last : (net depth (coarse depth configuration)).V) :
    (net (depth + 1) configuration).underlyingGraph.edist
        ((actualOldEmbedding depth configuration).vertices first)
        ((actualOldEmbedding depth configuration).vertices last) =
      2 * (net depth (coarse depth configuration)).underlyingGraph.edist first last :=
  le_antisymm (actual_edist_le_twice depth configuration first last)
    (actual_twice_edist_le depth configuration first last)

/-- Ordinary graph distance is used only after proving reachability in the real source component. -/
theorem actual_source_dist_eq_twice (depth : ℕ) (configuration : Conf (depth + 1))
    (first last : (net depth (coarse depth configuration)).V)
    (firstActive : (net depth (coarse depth configuration)).EdgePath
      (net depth (coarse depth configuration)).a first)
    (lastActive : (net depth (coarse depth configuration)).EdgePath
      (net depth (coarse depth configuration)).a last) :
    (net (depth + 1) configuration).underlyingGraph.dist
        ((actualOldEmbedding depth configuration).vertices first)
        ((actualOldEmbedding depth configuration).vertices last) =
      2 * (net depth (coarse depth configuration)).underlyingGraph.dist first last := by
  have coarseReachable := (TTN.edgePath_iff_reachable _ first last).mp
    (TTN.edgePath_trans (TTN.edgePath_symm firstActive) lastActive)
  have fineReachable := (actual_old_reachable_iff depth configuration first last).mpr coarseReachable
  have equality := actual_old_edist_eq_twice depth configuration first last
  rw [← fineReachable.coe_dist_eq_edist, ← coarseReachable.coe_dist_eq_edist] at equality
  exact ENat.coe_inj.mp (by simpa only [ENat.coe_mul] using equality)

end Outlook.FourColourActualMetric

#print axioms Outlook.FourColourActualMetric.actual_walk_compression
#print axioms Outlook.FourColourActualMetric.actual_twice_edist_le
#print axioms Outlook.FourColourActualMetric.actual_old_edist_eq_twice
#print axioms Outlook.FourColourActualMetric.actual_source_dist_eq_twice
