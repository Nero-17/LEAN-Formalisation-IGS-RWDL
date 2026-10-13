import RequestProject.Outlook.FourColourActualMetric
import Mathlib.Topology.MetricSpace.Isometry

/-! Actual source-cluster mesh and the distance-normalized old-vertex isometry.
All vertex spaces are the genuine source components. No GH or GHP assertion is made. -/
namespace Outlook.FourColourActualMesh
open Cluster Outlook.FourColourActualCoarseEmbedding Outlook.FourColourActualCoarseRetraction
open Outlook.FourColourActualLengthInterface Outlook.FourColourActualMetric

/-- Every fine active vertex is old or adjacent to an actual coarse active old image. -/
theorem actual_mesh_neighbor (depth : ℕ) (configuration : Conf (depth + 1))
    (vertex : (net (depth + 1) configuration).V)
    (active : (net (depth + 1) configuration).EdgePath (net (depth + 1) configuration).a vertex) :
    ∃ original : (net depth (coarse depth configuration)).V,
      (net depth (coarse depth configuration)).EdgePath (net depth (coarse depth configuration)).a original ∧
      ((net (depth + 1) configuration).underlyingGraph.Adj vertex
        ((actualOldEmbedding depth configuration).vertices original) ∨
       vertex = (actualOldEmbedding depth configuration).vertices original) := by
  by_cases oldVertex : (actualPartition depth configuration).old vertex = true
  · obtain ⟨original, imageEqual⟩ := (actual_old_image_iff depth configuration vertex).mp oldVertex
    have oldActive : (net depth (coarse depth configuration)).EdgePath
        (net depth (coarse depth configuration)).a original := by
      apply (actual_source_membership_iff depth configuration original).mp
      rw [imageEqual]
      exact active
    exact ⟨original, oldActive, Or.inr imageEqual.symm⟩
  · have newVertex : (actualPartition depth configuration).old vertex = false := by
      cases value : (actualPartition depth configuration).old vertex <;> simp_all
    have notSource : vertex ≠ (net (depth + 1) configuration).a := by
      intro equality
      apply oldVertex
      rw [equality]
      exact (actualPartition depth configuration).source
    obtain ⟨walk⟩ := (TTN.edgePath_iff_reachable _ _ _).mp active
    obtain ⟨neighbor, adjacent, remainder, _⟩ :=
      SimpleGraph.Walk.exists_eq_cons_of_ne notSource walk.reverse
    have different := (actualPartition depth configuration).adjacent_alternates adjacent
    have neighborOld : (actualPartition depth configuration).old neighbor = true := by
      rw [newVertex] at different
      cases value : (actualPartition depth configuration).old neighbor <;> simp_all
    obtain ⟨original, imageEqual⟩ := (actual_old_image_iff depth configuration neighbor).mp neighborOld
    have neighborActive : (net (depth + 1) configuration).EdgePath (net (depth + 1) configuration).a neighbor :=
      (TTN.edgePath_iff_reachable _ _ _).mpr ⟨remainder.reverse⟩
    have oldActive : (net depth (coarse depth configuration)).EdgePath
        (net depth (coarse depth configuration)).a original := by
      apply (actual_source_membership_iff depth configuration original).mp
      rw [imageEqual]
      exact neighborActive
    refine ⟨original, oldActive, Or.inl ?_⟩
    rw [imageEqual]
    exact adjacent

theorem actual_mesh_distance (depth : ℕ) (configuration : Conf (depth + 1))
    (vertex : (net (depth + 1) configuration).V)
    (active : (net (depth + 1) configuration).EdgePath (net (depth + 1) configuration).a vertex) :
    ∃ original : (net depth (coarse depth configuration)).V,
      (net depth (coarse depth configuration)).EdgePath (net depth (coarse depth configuration)).a original ∧
      (net (depth + 1) configuration).underlyingGraph.dist vertex
        ((actualOldEmbedding depth configuration).vertices original) ≤ 1 := by
  obtain ⟨original, oldActive, adjacent | equality⟩ := actual_mesh_neighbor depth configuration vertex active
  · exact ⟨original, oldActive, SimpleGraph.dist_le adjacent.toWalk⟩
  · refine ⟨original, oldActive, ?_⟩
    rw [equality, SimpleGraph.dist_self]
    exact Nat.zero_le 1

/-- The actual source component, retaining its generation and configuration as type indices. -/
def SourceSpace (depth : ℕ) (configuration : Conf depth) : Type :=
  {vertex : (net depth configuration).V // (net depth configuration).EdgePath (net depth configuration).a vertex}

noncomputable def distanceScale (depth : ℕ) : ℝ := ((2 : ℝ) ^ depth)⁻¹

theorem distanceScale_pos (depth : ℕ) : 0 < distanceScale depth := by
  unfold distanceScale
  positivity

theorem distanceScale_succ_double (depth : ℕ) : distanceScale (depth + 1) * 2 = distanceScale depth := by
  unfold distanceScale
  rw [pow_succ, mul_inv_rev]
  ring

private theorem source_reachable (depth : ℕ) (configuration : Conf depth)
    (first last : SourceSpace depth configuration) :
    (net depth configuration).underlyingGraph.Reachable first.1 last.1 :=
  (TTN.edgePath_iff_reachable _ _ _).mp (TTN.edgePath_trans (TTN.edgePath_symm first.2) last.2)

noncomputable instance sourceMetricSpace (depth : ℕ) (configuration : Conf depth) :
    MetricSpace (SourceSpace depth configuration) where
  dist first last := distanceScale depth * ((net depth configuration).underlyingGraph.dist first.1 last.1 : ℝ)
  dist_self := by
    intro vertex
    rw [SimpleGraph.dist_self]
    simp
  dist_comm := by
    intro first last
    rw [SimpleGraph.dist_comm]
  dist_triangle := by
    intro first middle last
    have bound := (source_reachable depth configuration first middle).dist_triangle_left last.1
    have realBound : ((net depth configuration).underlyingGraph.dist first.1 last.1 : ℝ) ≤
        ((net depth configuration).underlyingGraph.dist first.1 middle.1 : ℝ) +
        ((net depth configuration).underlyingGraph.dist middle.1 last.1 : ℝ) := by
      exact_mod_cast bound
    calc
      _ ≤ distanceScale depth *
          (((net depth configuration).underlyingGraph.dist first.1 middle.1 : ℝ) +
           ((net depth configuration).underlyingGraph.dist middle.1 last.1 : ℝ)) :=
        mul_le_mul_of_nonneg_left realBound (le_of_lt (distanceScale_pos depth))
      _ = _ := mul_add _ _ _
  eq_of_dist_eq_zero := by
    intro first last equality
    have realZero : ((net depth configuration).underlyingGraph.dist first.1 last.1 : ℝ) = 0 :=
      (mul_eq_zero.mp equality).resolve_left (ne_of_gt (distanceScale_pos depth))
    have naturalZero : (net depth configuration).underlyingGraph.dist first.1 last.1 = 0 := by
      exact_mod_cast realZero
    apply Subtype.ext
    exact (source_reachable depth configuration first last).dist_eq_zero_iff.mp naturalZero

def oldSourceEmbedding (depth : ℕ) (configuration : Conf (depth + 1)) :
    SourceSpace depth (coarse depth configuration) ↪ SourceSpace (depth + 1) configuration where
  toFun vertex := ⟨(actualOldEmbedding depth configuration).vertices vertex.1,
    actual_source_membership_forward depth configuration vertex.1 vertex.2⟩
  inj' := by
    intro first last equality
    apply Subtype.ext
    exact (actualOldEmbedding depth configuration).vertices.injective (congrArg Subtype.val equality)

/-- The scale is2^(-depth); exact real source distances make the old map an isometry. -/
theorem actual_normalized_isometry (depth : ℕ) (configuration : Conf (depth + 1)) :
    Isometry (oldSourceEmbedding depth configuration) := by
  apply Isometry.of_dist_eq
  intro first last
  change distanceScale (depth + 1) *
      ((net (depth + 1) configuration).underlyingGraph.dist
        ((actualOldEmbedding depth configuration).vertices first.1)
        ((actualOldEmbedding depth configuration).vertices last.1) : ℝ) =
    distanceScale depth * ((net depth (coarse depth configuration)).underlyingGraph.dist first.1 last.1 : ℝ)
  rw [actual_source_dist_eq_twice depth configuration first.1 last.1 first.2 last.2]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [← mul_assoc, distanceScale_succ_double]

/-- Every fine source point is within the actual next-generation mesh of the old active image. -/
theorem actual_normalized_mesh (depth : ℕ) (configuration : Conf (depth + 1))
    (vertex : SourceSpace (depth + 1) configuration) :
    ∃ original : SourceSpace depth (coarse depth configuration),
      dist vertex (oldSourceEmbedding depth configuration original) ≤ distanceScale (depth + 1) := by
  obtain ⟨original, oldActive, bound⟩ := actual_mesh_distance depth configuration vertex.1 vertex.2
  refine ⟨⟨original, oldActive⟩, ?_⟩
  change distanceScale (depth + 1) *
      ((net (depth + 1) configuration).underlyingGraph.dist vertex.1
        ((actualOldEmbedding depth configuration).vertices original) : ℝ) ≤ distanceScale (depth + 1)
  have realBound : ((net (depth + 1) configuration).underlyingGraph.dist vertex.1
      ((actualOldEmbedding depth configuration).vertices original) : ℝ) ≤ 1 := by
    exact_mod_cast bound
  calc
    _ ≤ distanceScale (depth + 1) * 1 :=
      mul_le_mul_of_nonneg_left realBound (le_of_lt (distanceScale_pos (depth + 1)))
    _ = _ := mul_one _

end Outlook.FourColourActualMesh

#print axioms Outlook.FourColourActualMesh.actual_mesh_neighbor
#print axioms Outlook.FourColourActualMesh.actual_mesh_distance
#print axioms Outlook.FourColourActualMesh.sourceMetricSpace
#print axioms Outlook.FourColourActualMesh.actual_normalized_isometry
#print axioms Outlook.FourColourActualMesh.actual_normalized_mesh
