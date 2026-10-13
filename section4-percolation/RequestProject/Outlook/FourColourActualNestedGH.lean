import RequestProject.Outlook.FourColourActualCompactGH
import RequestProject.Cluster.NestedReduction

/-! The actual critical nested-cluster process supplies the structural compatibility
internally. Each finite law is the original Bernoulli(pc) law conditioned on terminal
connection. The compact metric limit here is constructed pathwise on this actual
sample space; measurability of its GH class and metric-measure laws are separate. -/
noncomputable section
namespace Outlook.FourColourActualNestedGH
open Cluster Reduced MeasureTheory Filter Topology
open FourColourActualMesh FourColourActualCompletion FourColourActualCompactGH

/-- This is the existing actual coupled configuration process, not an independently
sampled family of marginal clusters or a postulated compatible family. -/
def actualNestedFamily (cluster : NestedCluster) : CompatibleConfigurations where
  configuration depth := nestedConfiguration depth cluster
  bonded depth := nestedConfiguration_bonded cluster depth

abbrev NestedStage (cluster : NestedCluster) (depth : ℕ) := Stage (actualNestedFamily cluster) depth
abbrev NestedCompletion (cluster : NestedCluster) := SourceCompletion (actualNestedFamily cluster)

theorem actual_nested_bonded (cluster : NestedCluster) (depth : ℕ) :
    coarse depth ((actualNestedFamily cluster).configuration (depth + 1)) =
      (actualNestedFamily cluster).configuration depth :=
  nestedConfiguration_bonded cluster depth

/-- The precise critical finite law used by this construction. -/
theorem actual_nested_critical_law (depth : ℕ) :
    nestedClusterMeasure.map (fun cluster => (actualNestedFamily cluster).configuration depth) =
      ProbabilityTheory.cond (confMeasure pc depth) (connSet depth) :=
  nestedConfiguration_law depth

/-- The chosen actual old embeddings are normalized source isometries on every sample. -/
theorem actual_nested_isometry (cluster : NestedCluster) (depth : ℕ) :
    Isometry (nextStage (actualNestedFamily cluster) depth) :=
  nextStage_isometry (actualNestedFamily cluster) depth

/-- The same actual old embeddings commute inside the constructed compact completion. -/
theorem actual_nested_completion_commute (cluster : NestedCluster) (depth : ℕ)
    (vertex : NestedStage cluster depth) :
    toCompletion (actualNestedFamily cluster) (depth + 1)
        (nextStage (actualNestedFamily cluster) depth vertex) =
      toCompletion (actualNestedFamily cluster) depth vertex :=
  toCompletion_commute (actualNestedFamily cluster) depth vertex

/-- No external configuration compatibility or geometric premise occurs here. -/
theorem actual_nested_gh_bound (cluster : NestedCluster) (depth : ℕ) :
    GromovHausdorff.ghDist (NestedStage cluster depth) (NestedCompletion cluster) ≤ distanceScale depth :=
  completion_gh_bound (actualNestedFamily cluster) depth

theorem actual_nested_gh_convergence (cluster : NestedCluster) :
    Tendsto (fun depth => GromovHausdorff.ghDist (NestedStage cluster depth) (NestedCompletion cluster))
      atTop (𝓝 0) :=
  completion_gh_tendsto_zero (actualNestedFamily cluster)

/-- On the original critical probability space, the red-conditioned interpretation
and the pathwise compact-source GH limit hold on one common full-measure event. -/
theorem actual_nested_critical_connected_gh :
    ∀ᵐ cluster ∂nestedClusterMeasure,
      (∀ depth, conn depth (nestedConfiguration depth cluster) = true) ∧
      (∀ depth, GromovHausdorff.ghDist (NestedStage cluster depth) (NestedCompletion cluster) ≤ distanceScale depth) ∧
      Tendsto (fun depth => GromovHausdorff.ghDist (NestedStage cluster depth) (NestedCompletion cluster))
        atTop (𝓝 0) := by
  filter_upwards [nestedConfiguration_connected] with cluster connected
  exact ⟨connected, actual_nested_gh_bound cluster, actual_nested_gh_convergence cluster⟩

end Outlook.FourColourActualNestedGH

#print axioms Outlook.FourColourActualNestedGH.actualNestedFamily
#print axioms Outlook.FourColourActualNestedGH.actual_nested_critical_law
#print axioms Outlook.FourColourActualNestedGH.actual_nested_isometry
#print axioms Outlook.FourColourActualNestedGH.actual_nested_completion_commute
#print axioms Outlook.FourColourActualNestedGH.actual_nested_gh_bound
#print axioms Outlook.FourColourActualNestedGH.actual_nested_gh_convergence
#print axioms Outlook.FourColourActualNestedGH.actual_nested_critical_connected_gh
