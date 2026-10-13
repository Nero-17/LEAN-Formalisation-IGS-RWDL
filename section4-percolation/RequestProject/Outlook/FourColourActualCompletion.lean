import RequestProject.Outlook.FourColourActualMesh
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.Completion

/-! A coherent completion of actual source components for a genuinely bonded
configuration family. Bonding is structural data, not an assumed geometric law.
Compactness and quantitative GH convergence require the remaining tail estimate. -/
noncomputable section

namespace Outlook.FourColourActualCompletion
open Cluster Outlook.FourColourActualMesh
open Set

/-- The original Conf/coarse compatibility, with no metric assumption. -/
structure CompatibleConfigurations where
  configuration : (depth : ℕ) → Conf depth
  bonded : ∀ depth, coarse depth (configuration (depth + 1)) = configuration depth

/-- Transport between equal actual configurations transports their defined metrics. -/
def configurationTransport (depth : ℕ) (first last : Conf depth) (equality : first = last) :
    SourceSpace depth first ≃ᵢ SourceSpace depth last := by
  subst last
  exact IsometryEquiv.refl _

abbrev Stage (family : CompatibleConfigurations) (depth : ℕ) :=
  SourceSpace depth (family.configuration depth)

instance stageFinite (family : CompatibleConfigurations) (depth : ℕ) : Finite (Stage family depth) := by
  change Finite {vertex : (net depth (family.configuration depth)).V //
    (net depth (family.configuration depth)).EdgePath (net depth (family.configuration depth)).a vertex}
  infer_instance

instance stageCompactSpace (family : CompatibleConfigurations) (depth : ℕ) :
    CompactSpace (Stage family depth) := by infer_instance

def stageSource (family : CompatibleConfigurations) (depth : ℕ) : Stage family depth :=
  ⟨(net depth (family.configuration depth)).a, TTN.edgePath_self _ _⟩

/-- The actual old map, with only the configuration bonding equality transported. -/
def nextStage (family : CompatibleConfigurations) (depth : ℕ) :
    Stage family depth → Stage family (depth + 1) :=
  fun vertex => oldSourceEmbedding depth (family.configuration (depth + 1))
    (configurationTransport depth (family.configuration depth)
      (coarse depth (family.configuration (depth + 1))) (family.bonded depth).symm vertex)

theorem nextStage_isometry (family : CompatibleConfigurations) (depth : ℕ) :
    Isometry (nextStage family depth) :=
  (actual_normalized_isometry depth (family.configuration (depth + 1))).comp
    (configurationTransport depth (family.configuration depth)
      (coarse depth (family.configuration (depth + 1))) (family.bonded depth).symm).isometry

theorem nextStage_mesh (family : CompatibleConfigurations) (depth : ℕ)
    (vertex : Stage family (depth + 1)) :
    ∃ original : Stage family depth, dist vertex (nextStage family depth original) ≤ distanceScale (depth + 1) := by
  let transport := configurationTransport depth (family.configuration depth)
    (coarse depth (family.configuration (depth + 1))) (family.bonded depth).symm
  obtain ⟨original, bound⟩ := actual_normalized_mesh depth (family.configuration (depth + 1)) vertex
  refine ⟨transport.symm original, ?_⟩
  simpa only [nextStage, transport, IsometryEquiv.apply_symm_apply] using bound

/-- The actual coherent source-space union, identifying the actual old isometric maps. -/
def SourceInductiveLimit (family : CompatibleConfigurations) : Type :=
  Metric.InductiveLimit (f := nextStage family) (nextStage_isometry family)

noncomputable instance inductiveLimitMetricSpace (family : CompatibleConfigurations) :
    MetricSpace (SourceInductiveLimit family) :=
  inferInstanceAs (MetricSpace (Metric.InductiveLimit (f := nextStage family) (nextStage_isometry family)))

def toInductiveLimit (family : CompatibleConfigurations) (depth : ℕ) :
    Stage family depth → SourceInductiveLimit family :=
  Metric.toInductiveLimit (nextStage_isometry family) depth

theorem toInductiveLimit_isometry (family : CompatibleConfigurations) (depth : ℕ) :
    Isometry (toInductiveLimit family depth) :=
  Metric.toInductiveLimit_isometry (nextStage_isometry family) depth

theorem toInductiveLimit_commute (family : CompatibleConfigurations) (depth : ℕ)
    (vertex : Stage family depth) :
    toInductiveLimit family (depth + 1) (nextStage family depth vertex) =
      toInductiveLimit family depth vertex :=
  congrFun (Metric.toInductiveLimit_commute (nextStage_isometry family) depth) vertex

/-- The genuine metric completion of the compatible actual source union. -/
def SourceCompletion (family : CompatibleConfigurations) : Type :=
  UniformSpace.Completion (SourceInductiveLimit family)

noncomputable instance completionMetricSpace (family : CompatibleConfigurations) :
    MetricSpace (SourceCompletion family) :=
  inferInstanceAs (MetricSpace (UniformSpace.Completion (SourceInductiveLimit family)))

instance completionCompleteSpace (family : CompatibleConfigurations) :
    CompleteSpace (SourceCompletion family) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (SourceInductiveLimit family)))

def toCompletion (family : CompatibleConfigurations) (depth : ℕ) (vertex : Stage family depth) :
    SourceCompletion family :=
  (toInductiveLimit family depth vertex : UniformSpace.Completion (SourceInductiveLimit family))

theorem toCompletion_isometry (family : CompatibleConfigurations) (depth : ℕ) :
    Isometry (toCompletion family depth) :=
  UniformSpace.Completion.coe_isometry.comp (toInductiveLimit_isometry family depth)

theorem toCompletion_commute (family : CompatibleConfigurations) (depth : ℕ)
    (vertex : Stage family depth) :
    toCompletion family (depth + 1) (nextStage family depth vertex) = toCompletion family depth vertex :=
  congrArg (fun point : SourceInductiveLimit family =>
    (point : UniformSpace.Completion (SourceInductiveLimit family)))
      (toInductiveLimit_commute family depth vertex)

instance completionNonempty (family : CompatibleConfigurations) : Nonempty (SourceCompletion family) :=
  ⟨toCompletion family 0 (stageSource family 0)⟩

theorem stageRange_compact (family : CompatibleConfigurations) (depth : ℕ) :
    IsCompact (range (toCompletion family depth)) :=
  isCompact_range (toCompletion_isometry family depth).continuous

theorem stages_dense_in_completion (family : CompatibleConfigurations) :
    Dense (⋃ depth, range (toCompletion family depth)) := by
  have denseStages : Dense (⋃ depth, range (toInductiveLimit family depth)) :=
    Metric.dense_iUnion_range_toInductiveLimit (nextStage_isometry family)
  have denseImage :=
    (UniformSpace.Completion.denseRange_coe (α := SourceInductiveLimit family)).dense_image
      UniformSpace.Completion.coe_isometry.continuous denseStages
  refine denseImage.mono ?_
  rintro point ⟨original, membership, rfl⟩
  rcases mem_iUnion.mp membership with ⟨depth, vertex, rfl⟩
  exact mem_iUnion.mpr ⟨depth, vertex, rfl⟩

/-- The actual next-generation mesh estimate is retained in the coherent completion. -/
theorem completion_one_step_mesh (family : CompatibleConfigurations) (depth : ℕ)
    (vertex : Stage family (depth + 1)) :
    ∃ original : Stage family depth,
      dist (toCompletion family (depth + 1) vertex) (toCompletion family depth original) ≤
        distanceScale (depth + 1) := by
  obtain ⟨original, bound⟩ := nextStage_mesh family depth vertex
  refine ⟨original, ?_⟩
  rw [← toCompletion_commute family depth original,
    (toCompletion_isometry family (depth + 1)).dist_eq]
  exact bound

/-- Finite geometric tails in the actual common completion telescope exactly. -/
theorem completion_finite_tail (family : CompatibleConfigurations) :
    ∀ highest depth : ℕ, depth ≤ highest → ∀ vertex : Stage family highest,
      ∃ original : Stage family depth,
        dist (toCompletion family highest vertex) (toCompletion family depth original) ≤
          distanceScale depth - distanceScale highest := by
  intro highest
  induction highest with
  | zero =>
      intro depth lowerBound vertex
      have depthZero : depth = 0 := Nat.eq_zero_of_le_zero lowerBound
      subst depth
      exact ⟨vertex, by simp only [dist_self, sub_self, le_refl]⟩
  | succ highest induction =>
      intro depth lowerBound vertex
      by_cases lastLevel : depth = highest + 1
      · subst depth
        exact ⟨vertex, by simp only [dist_self, sub_self, le_refl]⟩
      · have lowerBoundPrevious : depth ≤ highest := by omega
        obtain ⟨parent, parentBound⟩ := completion_one_step_mesh family highest vertex
        obtain ⟨original, previousBound⟩ := induction depth lowerBoundPrevious parent
        refine ⟨original, ?_⟩
        calc
          _ ≤ dist (toCompletion family (highest + 1) vertex) (toCompletion family highest parent) +
              dist (toCompletion family highest parent) (toCompletion family depth original) :=
            dist_triangle _ _ _
          _ ≤ distanceScale (highest + 1) + (distanceScale depth - distanceScale highest) :=
            add_le_add parentBound previousBound
          _ = distanceScale depth - distanceScale (highest + 1) := by
            nlinarith [distanceScale_succ_double highest]

end Outlook.FourColourActualCompletion

#print axioms Outlook.FourColourActualCompletion.nextStage_isometry
#print axioms Outlook.FourColourActualCompletion.toCompletion_isometry
#print axioms Outlook.FourColourActualCompletion.toCompletion_commute
#print axioms Outlook.FourColourActualCompletion.stages_dense_in_completion
#print axioms Outlook.FourColourActualCompletion.completion_one_step_mesh

#print axioms Outlook.FourColourActualCompletion.completion_finite_tail
