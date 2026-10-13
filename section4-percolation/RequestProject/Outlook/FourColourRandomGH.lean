import RequestProject.Outlook.FourColourActualNestedGH
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! A measurable random compact metric source space on the original critical
NestedCluster sample space. The random object is its GH isometry class; no
vertex/speed measure or GHP statement is introduced. -/
noncomputable section
namespace Outlook.FourColourRandomGH
open Cluster Reduced MeasureTheory Filter Topology
open FourColourActualMesh FourColourActualNestedGH

instance ghMeasurableSpace : MeasurableSpace GromovHausdorff.GHSpace :=
  borel GromovHausdorff.GHSpace

instance ghBorelSpace : BorelSpace GromovHausdorff.GHSpace := ⟨rfl⟩

instance sourceSpaceFinite (depth : ℕ) (configuration : Conf depth) :
    Finite (SourceSpace depth configuration) := by
  change Finite {vertex : (net depth configuration).V //
    (net depth configuration).EdgePath (net depth configuration).a vertex}
  infer_instance

instance sourceSpaceNonempty (depth : ℕ) (configuration : Conf depth) :
    Nonempty (SourceSpace depth configuration) :=
  ⟨⟨(net depth configuration).a, TTN.edgePath_self _ _⟩⟩

instance sourceSpaceCompact (depth : ℕ) (configuration : Conf depth) :
    CompactSpace (SourceSpace depth configuration) := by infer_instance

/-- The actual normalized finite source graph, taken up to metric isometry. -/
def finiteSourceGH (depth : ℕ) (configuration : Conf depth) : GromovHausdorff.GHSpace :=
  GromovHausdorff.toGHSpace (SourceSpace depth configuration)

theorem measurable_finiteSourceGH (depth : ℕ) : Measurable (finiteSourceGH depth) :=
  Measurable.of_discrete

def actualFiniteGH (depth : ℕ) (cluster : NestedCluster) : GromovHausdorff.GHSpace :=
  finiteSourceGH depth (nestedConfiguration depth cluster)

theorem measurable_actualFiniteGH (depth : ℕ) : Measurable (actualFiniteGH depth) :=
  (measurable_finiteSourceGH depth).comp (measurable_nestedConfiguration depth)

/-- The isometry class of the actual compact completion already constructed per sample. -/
def actualCompactGH (cluster : NestedCluster) : GromovHausdorff.GHSpace :=
  GromovHausdorff.toGHSpace (NestedCompletion cluster)

/-- The measurable finite-level classes converge to this actual completion class at every sample. -/
theorem actualFiniteGH_tendsto (cluster : NestedCluster) :
    Tendsto (fun depth => actualFiniteGH depth cluster) atTop (𝓝 (actualCompactGH cluster)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact actual_nested_gh_convergence cluster

theorem actualFiniteGH_dist_bound (cluster : NestedCluster) (depth : ℕ) :
    dist (actualFiniteGH depth cluster) (actualCompactGH cluster) ≤ distanceScale depth :=
  actual_nested_gh_bound cluster depth

/-- Pointwise convergence in the genuine metrizable Borel GH space proves measurability. -/
theorem measurable_actualCompactGH : Measurable actualCompactGH := by
  apply measurable_of_tendsto_metrizable (fun depth => measurable_actualFiniteGH depth)
  exact tendsto_pi_nhds.mpr actualFiniteGH_tendsto

def actualGHPath (cluster : NestedCluster) (depth : ℕ) : GromovHausdorff.GHSpace :=
  actualFiniteGH depth cluster

theorem measurable_actualGHPath : Measurable actualGHPath :=
  measurable_pi_lambda _ (fun depth => measurable_actualFiniteGH depth)

/-- The exact finite-level law is the original critical percolation law conditioned on connection. -/
theorem actual_finite_gh_law (depth : ℕ) :
    nestedClusterMeasure.map (actualFiniteGH depth) =
      (ProbabilityTheory.cond (confMeasure pc depth) (connSet depth)).map (finiteSourceGH depth) := by
  have equality := congrArg (fun measure : Measure (Conf depth) => measure.map (finiteSourceGH depth))
    (nestedConfiguration_law depth)
  dsimp only at equality
  rw [Measure.map_map (measurable_finiteSourceGH depth) (measurable_nestedConfiguration depth)] at equality
  exact equality

/-- A genuine probability law on compact metric source-space isometry classes. -/
def compactSourceLaw : Measure GromovHausdorff.GHSpace :=
  nestedClusterMeasure.map actualCompactGH

instance compactSourceLaw_probability : IsProbabilityMeasure compactSourceLaw :=
  Measure.isProbabilityMeasure_map measurable_actualCompactGH.aemeasurable

theorem actual_gh_ae_limit :
    ∀ᵐ cluster ∂nestedClusterMeasure,
      Tendsto (fun depth => actualFiniteGH depth cluster) atTop (𝓝 (actualCompactGH cluster)) :=
  Filter.Eventually.of_forall actualFiniteGH_tendsto

end Outlook.FourColourRandomGH

#print axioms Outlook.FourColourRandomGH.measurable_actualFiniteGH
#print axioms Outlook.FourColourRandomGH.actualFiniteGH_tendsto
#print axioms Outlook.FourColourRandomGH.measurable_actualCompactGH
#print axioms Outlook.FourColourRandomGH.measurable_actualGHPath
#print axioms Outlook.FourColourRandomGH.actual_finite_gh_law
#print axioms Outlook.FourColourRandomGH.compactSourceLaw_probability
