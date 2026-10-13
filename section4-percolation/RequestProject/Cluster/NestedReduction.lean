import RequestProject.Cluster.InfiniteProcess
import RequestProject.Cluster.InfiniteTree

/-!
# Pathwise reduction of the genuine infinite critical cluster

Reduction is one measurable map of infinite compatible configuration paths
to infinite compatible trees. It preserves the full resistance sequence
almost surely, and the image trees have the prescribed finite branching laws.
-/

namespace Cluster

open MeasureTheory ProbabilityTheory Reduced

noncomputable section

/-- Reduce every level of one infinite cluster, retaining its ancestor choices. -/
def nestedClusterTree (cluster : NestedCluster) : NestedTree :=
  ⟨fun n => Phi n (nestedConfiguration n cluster), fun n => by
    rw [rtrunc_Phi, nestedConfiguration_bonded]⟩

theorem measurable_nestedClusterTree : Measurable nestedClusterTree := by
  apply Measurable.subtype_mk
  exact measurable_pi_lambda _ (fun n =>
    (measurable_Phi n).comp (measurable_nestedConfiguration n))

/-- The reduction has exactly the paper's finite independently branching tree laws. -/
theorem nestedClusterTree_law (n : ℕ) :
    nestedClusterMeasure.map (fun cluster => nestedTree n (nestedClusterTree cluster)) =
      rMeasure (pdiamond pc) (pseries pc) n := by
  have critical_mass_ne_zero : ENNReal.ofReal pc ≠ 0 := by simp [pc_pos]
  change nestedClusterMeasure.map (Phi n ∘ nestedConfiguration n) = _
  rw [← Measure.map_map (measurable_Phi n) (measurable_nestedConfiguration n),
    nestedConfiguration_law, connectedMeasure, ProbabilityTheory.cond,
    confMeasure_connSet, Measure.map_smul, Phi_pushforward, smul_smul,
    ENNReal.inv_mul_cancel critical_mass_ne_zero ENNReal.ofReal_ne_top, one_smul]

/-- Every level is connected, simultaneously, outside one null set. -/
theorem nestedConfiguration_connected :
    ∀ᵐ cluster ∂nestedClusterMeasure, ∀ n, conn n (nestedConfiguration n cluster) = true := by
  apply ae_all_iff.mpr
  intro n
  have connected_support : ∀ᵐ configuration ∂connectedMeasure n,
      configuration ∈ connSet n :=
    ProbabilityTheory.ae_cond_mem (measurableSet_connSet n)
  rw [← nestedConfiguration_law n] at connected_support
  exact (ae_map_iff (measurable_nestedConfiguration n).aemeasurable
    (measurableSet_connSet n)).mp connected_support

/-- The complete resistance sequences agree on this coupling, not only one marginal. -/
theorem nested_reduction_resistance_sequence :
    ∀ᵐ cluster ∂nestedClusterMeasure, ∀ n,
      (res n (nestedConfiguration n cluster)).toReal =
        Rres n (nestedTree n (nestedClusterTree cluster)) := by
  filter_upwards [nestedConfiguration_connected] with cluster connected
  intro n
  exact toReal_res_eq_Rres n (nestedConfiguration n cluster) (connected n)

/-- Proposition 4.2 as equality of the joint laws of the full infinite sequences. -/
theorem nested_cluster_resistance_process :
    nestedClusterMeasure.map
      (fun cluster n => (res n (nestedConfiguration n cluster)).toReal) =
      (nestedClusterMeasure.map nestedClusterTree).map
        (fun tree n => Rres n (nestedTree n tree)) := by
  have measurable_reduced_sequence :
      Measurable (fun tree n => Rres n (nestedTree n tree)) :=
    measurable_pi_lambda _ (fun n =>
      (Measurable.of_discrete : Measurable (Rres n)).comp (measurable_nestedTree n))
  rw [Measure.map_map measurable_reduced_sequence measurable_nestedClusterTree]
  apply Measure.map_congr
  filter_upwards [nested_reduction_resistance_sequence] with cluster equality
  exact funext equality

end
end Cluster
