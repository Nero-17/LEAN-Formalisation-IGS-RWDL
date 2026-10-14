import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Tactic

/-! A single complete compact ambient for countably many compact extensions
of the same compact metric space. All embeddings preserve the given metrics.
The construction uses successive metric amalgamation, its metric inductive
limit, and completion; an ambient existence assumption is not an input.

Mathematical construction suggested by IGSIII34/Topology/
CommonTargetMetricAmalgamationCompletion.lean and
CommonTargetMetricCompactCompletion.lean at reference commit
cb0183af15f571bb0b1b5d3b8de367a419716f1b. The proof below is independently
organized for the RWDL Lean 4.28 interfaces. -/

namespace EIGS.CountableRealisation
noncomputable section
open Set Metric Filter
open scoped Topology
universe u

structure RootedMetricSpace (Root : Type u) [MetricSpace Root] where
  space : Type u
  metric : MetricSpace space
  root : Root → space
  root_isometry : Isometry root

attribute [local instance] RootedMetricSpace.metric

variable {Root : Type u} [MetricSpace Root] [Nonempty Root]
  (Extensions : ℕ → Type u) [∀ n, MetricSpace (Extensions n)]
  (roots : ∀ n, Root → Extensions n) (roots_isometry : ∀ n, Isometry (roots n))

def amalgamationStage : ℕ → RootedMetricSpace Root
  | 0 => ⟨Root, inferInstance, id, isometry_id⟩
  | n + 1 =>
    let previous := amalgamationStage n
    ⟨GlueSpace previous.root_isometry (roots_isometry n), inferInstance,
      toGlueL previous.root_isometry (roots_isometry n) ∘ previous.root,
      (toGlueL_isometry previous.root_isometry (roots_isometry n)).comp previous.root_isometry⟩

def amalgamationStep (n : ℕ) :
    (amalgamationStage Extensions roots roots_isometry n).space →
      (amalgamationStage Extensions roots roots_isometry (n + 1)).space :=
  toGlueL (amalgamationStage Extensions roots roots_isometry n).root_isometry
    (roots_isometry n)

theorem amalgamationStep_isometry (n : ℕ) :
    Isometry (amalgamationStep Extensions roots roots_isometry n) := toGlueL_isometry _ _

def AmalgamationUnion :=
  Metric.InductiveLimit (amalgamationStep_isometry Extensions roots roots_isometry)

instance countableRealisationUnionMetric :
    MetricSpace (AmalgamationUnion Extensions roots roots_isometry) :=
  inferInstanceAs (MetricSpace (Metric.InductiveLimit
    (amalgamationStep_isometry Extensions roots roots_isometry)))

def CompleteAmalgamation := UniformSpace.Completion
  (AmalgamationUnion Extensions roots roots_isometry)

instance countableRealisationAmbientMetric :
    MetricSpace (CompleteAmalgamation Extensions roots roots_isometry) :=
  inferInstanceAs (MetricSpace (UniformSpace.Completion
    (AmalgamationUnion Extensions roots roots_isometry)))

instance countableRealisationAmbientComplete :
    CompleteSpace (CompleteAmalgamation Extensions roots roots_isometry) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion
    (AmalgamationUnion Extensions roots roots_isometry)))

def rootInUnion : Root → AmalgamationUnion Extensions roots roots_isometry :=
  Metric.toInductiveLimit (amalgamationStep_isometry Extensions roots roots_isometry) 0

def extensionInUnion (n : ℕ) : Extensions n → AmalgamationUnion Extensions roots roots_isometry :=
  Metric.toInductiveLimit (amalgamationStep_isometry Extensions roots roots_isometry) (n + 1) ∘
    toGlueR (amalgamationStage Extensions roots roots_isometry n).root_isometry (roots_isometry n)

def rootInAmbient : Root → CompleteAmalgamation Extensions roots roots_isometry :=
  UniformSpace.Completion.coe' ∘ rootInUnion Extensions roots roots_isometry

def extensionInAmbient (n : ℕ) : Extensions n → CompleteAmalgamation Extensions roots roots_isometry :=
  UniformSpace.Completion.coe' ∘ extensionInUnion Extensions roots roots_isometry n

theorem rootInAmbient_isometry : Isometry (rootInAmbient Extensions roots roots_isometry) :=
  UniformSpace.Completion.coe_isometry.comp
    (Metric.toInductiveLimit_isometry (amalgamationStep_isometry Extensions roots roots_isometry) 0)

theorem extensionInAmbient_isometry (n : ℕ) :
    Isometry (extensionInAmbient Extensions roots roots_isometry n) :=
  UniformSpace.Completion.coe_isometry.comp
    ((Metric.toInductiveLimit_isometry (amalgamationStep_isometry Extensions roots roots_isometry) (n + 1)).comp
      (toGlueR_isometry _ _))

theorem stageRootInUnion (n : ℕ) (point : Root) :
    Metric.toInductiveLimit (amalgamationStep_isometry Extensions roots roots_isometry) n
      ((amalgamationStage Extensions roots roots_isometry n).root point) =
        rootInUnion Extensions roots roots_isometry point := by
  induction n with
  | zero => rfl
  | succ n induction =>
    have commute := congrFun
      (Metric.toInductiveLimit_commute (amalgamationStep_isometry Extensions roots roots_isometry) n)
      ((amalgamationStage Extensions roots roots_isometry n).root point)
    exact commute.trans induction

theorem extension_root_distance (n : ℕ) (point : Extensions n) (base : Root) :
    dist (extensionInAmbient Extensions roots roots_isometry n point)
      (rootInAmbient Extensions roots roots_isometry base) = dist point (roots n base) := by
  change dist (UniformSpace.Completion.coe' (extensionInUnion Extensions roots roots_isometry n point))
    (UniformSpace.Completion.coe' (rootInUnion Extensions roots roots_isometry base)) = _
  rw [UniformSpace.Completion.coe_isometry.dist_eq,
    ← stageRootInUnion Extensions roots roots_isometry (n + 1) base]
  have glued := congrFun (Metric.toGlue_commute
    (amalgamationStage Extensions roots roots_isometry n).root_isometry (roots_isometry n)) base
  change Metric.toGlueL _ _ ((amalgamationStage Extensions roots roots_isometry n).root base) =
    Metric.toGlueR _ _ (roots n base) at glued
  change dist (Metric.toInductiveLimit (amalgamationStep_isometry Extensions roots roots_isometry)
    (n + 1) (Metric.toGlueR (amalgamationStage Extensions roots roots_isometry n).root_isometry
      (roots_isometry n) point))
    (Metric.toInductiveLimit (amalgamationStep_isometry Extensions roots roots_isometry)
      (n + 1) (Metric.toGlueL (amalgamationStage Extensions roots roots_isometry n).root_isometry
        (roots_isometry n) ((amalgamationStage Extensions roots roots_isometry n).root base))) = _
  rw [glued, (Metric.toInductiveLimit_isometry
    (amalgamationStep_isometry Extensions roots roots_isometry) (n + 1)).dist_eq]
  exact (Metric.toGlueR_isometry _ _).dist_eq point (roots n base)

/-- Metric amalgamation and its inductive quotient introduce no extra points.
Only the final completion adds limits. -/
theorem union_point_cases (point : AmalgamationUnion Extensions roots roots_isometry) :
    (∃ base, point = rootInUnion Extensions roots roots_isometry base) ∨
      ∃ n value, point = extensionInUnion Extensions roots roots_isometry n value := by
  have atStage (n : ℕ) (value : (amalgamationStage Extensions roots roots_isometry n).space) :
      (∃ base, Metric.toInductiveLimit (amalgamationStep_isometry Extensions roots roots_isometry) n value =
        rootInUnion Extensions roots roots_isometry base) ∨
      ∃ index original, Metric.toInductiveLimit (amalgamationStep_isometry Extensions roots roots_isometry) n value =
        extensionInUnion Extensions roots roots_isometry index original := by
    induction n with
    | zero => exact Or.inl ⟨value, rfl⟩
    | succ n induction =>
      refine Quotient.inductionOn value ?_
      intro representative
      cases representative with
      | inr original => exact Or.inr ⟨n, original, rfl⟩
      | inl previous =>
        have commute := congrFun (Metric.toInductiveLimit_commute
          (amalgamationStep_isometry Extensions roots roots_isometry) n) previous
        change Metric.toInductiveLimit (amalgamationStep_isometry Extensions roots roots_isometry)
          (n + 1) (toGlueL (amalgamationStage Extensions roots roots_isometry n).root_isometry
            (roots_isometry n) previous) =
          Metric.toInductiveLimit (amalgamationStep_isometry Extensions roots roots_isometry)
            n previous at commute
        rcases induction previous with ⟨base, equal⟩ | ⟨index, original, equal⟩
        · exact Or.inl ⟨base, commute.trans equal⟩
        · exact Or.inr ⟨index, original, commute.trans equal⟩
  refine Quotient.inductionOn point ?_
  rintro ⟨n, value⟩
  exact atStage n value

/-- Compactness is proved from the compact prefix and a uniformly vanishing
tail distance to Root. It is not an additional ambient hypothesis. -/
theorem completeAmalgamation_compact [CompactSpace Root] [∀ n, CompactSpace (Extensions n)]
    (radii : ℕ → ℝ) (radiiZero : Tendsto radii atTop (𝓝 0))
    (closeToRoot : ∀ n point, ∃ base, dist point (roots n base) ≤ radii n) :
    CompactSpace (CompleteAmalgamation Extensions roots roots_isometry) := by
  have totallyBounded : TotallyBounded (range (UniformSpace.Completion.coe' :
      AmalgamationUnion Extensions roots roots_isometry →
        CompleteAmalgamation Extensions roots roots_isometry)) := by
    apply Metric.totallyBounded_iff.mpr
    intro epsilon positive
    obtain ⟨cutoff, tail⟩ := eventually_atTop.mp
      (radiiZero.eventually (gt_mem_nhds (half_pos positive)))
    let compactPrefix : Set (CompleteAmalgamation Extensions roots roots_isometry) :=
      range (rootInAmbient Extensions roots roots_isometry) ∪
        ⋃ n : Fin cutoff, range (extensionInAmbient Extensions roots roots_isometry n.val)
    have prefixCompact : IsCompact compactPrefix :=
      (isCompact_range (rootInAmbient_isometry Extensions roots roots_isometry).continuous).union
        (isCompact_iUnion fun n : Fin cutoff => isCompact_range
          (extensionInAmbient_isometry Extensions roots roots_isometry n.val).continuous)
    obtain ⟨centres, centresFinite, covers⟩ :=
      Metric.totallyBounded_iff.mp prefixCompact.totallyBounded (epsilon / 2) (half_pos positive)
    have nearPrefix (point : CompleteAmalgamation Extensions roots roots_isometry)
        (near : ∃ original ∈ compactPrefix, dist point original < epsilon / 2) :
        point ∈ ⋃ centre ∈ centres, Metric.ball centre epsilon := by
      obtain ⟨original, member, distance⟩ := near
      obtain ⟨centre, memberCentre⟩ := mem_iUnion.mp (covers member)
      obtain ⟨centreMember, originalDistance⟩ := mem_iUnion.mp memberCentre
      refine mem_iUnion.mpr ⟨centre, mem_iUnion.mpr ⟨centreMember, ?_⟩⟩
      exact (dist_triangle point original centre).trans_lt
        (add_lt_add distance originalDistance) |>.trans_eq (by ring)
    refine ⟨centres, centresFinite, ?_⟩
    rintro point ⟨original, rfl⟩
    apply nearPrefix
    rcases union_point_cases Extensions roots roots_isometry original with
      ⟨base, equal⟩ | ⟨n, value, equal⟩
    · rw [equal]
      exact ⟨rootInAmbient Extensions roots roots_isometry base, Or.inl (mem_range_self _),
        by
          change dist (rootInAmbient Extensions roots roots_isometry base)
            (rootInAmbient Extensions roots roots_isometry base) < epsilon / 2
          simpa only [dist_self] using half_pos positive⟩
    · rw [equal]
      by_cases early : n < cutoff
      · refine ⟨extensionInAmbient Extensions roots roots_isometry n value,
          Or.inr (mem_iUnion.mpr ⟨⟨n, early⟩, mem_range_self _⟩), ?_⟩
        change dist (extensionInAmbient Extensions roots roots_isometry n value)
          (extensionInAmbient Extensions roots roots_isometry n value) < epsilon / 2
        simpa only [dist_self] using half_pos positive
      · obtain ⟨base, near⟩ := closeToRoot n value
        refine ⟨rootInAmbient Extensions roots roots_isometry base, Or.inl (mem_range_self _), ?_⟩
        change dist (extensionInAmbient Extensions roots roots_isometry n value)
          (rootInAmbient Extensions roots roots_isometry base) < _
        rw [extension_root_distance]
        exact near.trans_lt (tail n (by omega))
  have closureCompact := totallyBounded.closure.isCompact_of_isClosed isClosed_closure
  rw [UniformSpace.Completion.denseRange_coe.closure_range] at closureCompact
  exact isCompact_univ_iff.mp closureCompact

end
end EIGS.CountableRealisation

#print axioms EIGS.CountableRealisation.extension_root_distance
#print axioms EIGS.CountableRealisation.completeAmalgamation_compact
