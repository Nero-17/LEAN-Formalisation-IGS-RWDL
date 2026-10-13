import RequestProject.Outlook.FourColourInfiniteProcess
import RequestProject.Cluster.NestedReduction

/-! Full joint laws of genuine source-cluster graphs under literal adopted
substitution. Graph shapes retain complete unlabelled graphs. This statement
does not construct a metric completion or a metric-measure scaling limit. -/
namespace Outlook.FourColourInfiniteGraphLaw
open Cluster MeasureTheory ProbabilityTheory
open FourColourConditionalHierarchy FourColourCodingTree FourColourActualGraphLaw
open FourColourLiteralRealization FourColourInfiniteProcess

noncomputable section

def actualClusterSequence (cluster : NestedCluster) (depth : ℕ) : SourceClusterShape :=
  sourceClusterShape (net depth (nestedConfiguration depth cluster))

def literalClusterSequence (path : (depth : ℕ) → RuleTree depth) (depth : ℕ) :
    SourceClusterShape := sourceClusterShape (literalRealize depth 0 (path depth))

theorem measurable_literalClusterSequence : Measurable literalClusterSequence :=
  measurable_pi_lambda _ (fun depth =>
    (Measurable.of_discrete : Measurable
      (fun tree => sourceClusterShape (literalRealize depth 0 tree))).comp (measurable_pi_apply depth))

/-- On one full-measure set, every actual finite cluster is the corresponding
literal substituted graph; simultaneous connection is the existing actual-process theorem. -/
theorem actual_literal_cluster_sequence :
    actualClusterSequence =ᵐ[nestedClusterMeasure]
      literalClusterSequence ∘ nestedEncodedSequence := by
  filter_upwards [nestedConfiguration_connected] with cluster connected
  funext depth
  have admissible : nestedConfiguration depth cluster ∈ parentEvent depth 0 := by
    change conn depth (nestedConfiguration depth cluster) = true
    exact connected depth
  exact Quotient.sound ⟨(literalRedClusterIso depth (nestedConfiguration depth cluster) admissible).symm⟩

/-- Equality of the entire source-cluster graph sequence law, not only its marginals. -/
theorem nested_cluster_full_literal_graph_law :
    nestedClusterMeasure.map actualClusterSequence =
      (ruleTreePathMeasure 0).map literalClusterSequence := by
  rw [Measure.map_congr actual_literal_cluster_sequence,
    ← Measure.map_map measurable_literalClusterSequence measurable_nestedEncodedSequence,
    nested_encoded_full_process_law]

/-- Every finite collection of cluster generations has the same joint graph law. -/
theorem nested_cluster_finite_joint_graph_law (indices : Finset ℕ) :
    nestedClusterMeasure.map (fun cluster => indices.restrict (actualClusterSequence cluster)) =
      (ruleTreePathMeasure 0).map (fun path => indices.restrict (literalClusterSequence path)) := by
  have measurable_restriction : Measurable
      (indices.restrict : (ℕ → SourceClusterShape) → (indices → SourceClusterShape)) :=
    measurable_pi_lambda _ (fun index => measurable_pi_apply index.val)
  have measurable_actual : Measurable actualClusterSequence :=
    measurable_pi_lambda _ (fun depth =>
      (Measurable.of_discrete : Measurable
        (fun configuration => sourceClusterShape (net depth configuration))).comp
          (measurable_nestedConfiguration depth))
  have equality := congrArg (fun measure => measure.map indices.restrict)
    nested_cluster_full_literal_graph_law
  dsimp only at equality
  rw [Measure.map_map measurable_restriction measurable_actual,
    Measure.map_map measurable_restriction measurable_literalClusterSequence] at equality
  exact equality

/-- The same full graph-sequence law on the original all-configuration path space. -/
theorem infinite_cluster_full_literal_graph_law :
    infiniteClusterMeasure.map
      (fun path depth => sourceClusterShape (net depth (path depth))) =
      (ruleTreePathMeasure 0).map literalClusterSequence := by
  have inclusion : nestedClusterMeasure.map Subtype.val = infiniteClusterMeasure :=
    InverseSystem.compatibleMeasure_map_val connectedMeasure coarse measurable_coarse
      connectedMeasure_map_coarse
  have measurable_graphs : Measurable
      (fun (path : (depth : ℕ) → Conf depth) depth => sourceClusterShape (net depth (path depth))) :=
    measurable_pi_lambda _ (fun depth =>
      (Measurable.of_discrete : Measurable
        (fun configuration => sourceClusterShape (net depth configuration))).comp (measurable_pi_apply depth))
  rw [← inclusion, Measure.map_map measurable_graphs measurable_subtype_coe]
  exact nested_cluster_full_literal_graph_law

end
end Outlook.FourColourInfiniteGraphLaw

#print axioms Outlook.FourColourInfiniteGraphLaw.actual_literal_cluster_sequence
#print axioms Outlook.FourColourInfiniteGraphLaw.nested_cluster_full_literal_graph_law
#print axioms Outlook.FourColourInfiniteGraphLaw.nested_cluster_finite_joint_graph_law
#print axioms Outlook.FourColourInfiniteGraphLaw.infinite_cluster_full_literal_graph_law
