import RequestProject.Cluster.InverseLimit
import RequestProject.Cluster.Coupling
import RequestProject.Cluster.Exponent
import RequestProject.Reduced.AllParameters

/-!
# The infinite nested critical cluster

This construction uses the actual critical percolation configuration laws.
The finer configuration is sampled from its conditional distribution given
its coarse image. The resulting probability measure is concentrated on
compatible infinite configuration paths. Reduction by `Phi` therefore also
gives one compatible infinite substitution-tree process.
-/

namespace Cluster

open MeasureTheory ProbabilityTheory Filter Topology Reduced

noncomputable section

instance instConfNonempty : (n : ℕ) → Nonempty (Conf n)
  | 0 => inferInstanceAs (Nonempty Bool)
  | n + 1 =>
      let _ := instConfNonempty n
      inferInstanceAs (Nonempty (Conf n × Conf n × Conf n × Conf n))

/-- Critical percolation conditioned on the terminals being connected. -/
def connectedMeasure (n : ℕ) : Measure (Conf n) :=
  ProbabilityTheory.cond (confMeasure pc n) (connSet n)

instance connectedMeasure_probability (n : ℕ) : IsProbabilityMeasure (connectedMeasure n) := by
  haveI := isProb_confMeasure pc_nonneg pc_le_one n
  apply ProbabilityTheory.cond_isProbabilityMeasure
  rw [confMeasure_connSet]
  simp [pc_pos]

lemma coarse_preimage_connSet (n : ℕ) :
    (coarse n) ⁻¹' connSet n = connSet (n + 1) := by
  ext configuration
  simp only [Set.mem_preimage, connSet, Set.mem_setOf_eq, conn_coarse]

/-- The conditioned laws are consistent under genuine coarse-graining. -/
theorem connectedMeasure_map_coarse (n : ℕ) :
    (connectedMeasure (n + 1)).map (coarse n) = connectedMeasure n := by
  rw [connectedMeasure, connectedMeasure, ProbabilityTheory.cond,
    ProbabilityTheory.cond, Measure.map_smul, confMeasure_connSet,
    confMeasure_connSet, ← coarse_preimage_connSet,
    ← Measure.restrict_map (measurable_coarse n) (measurableSet_connSet n),
    confMeasure_map_coarse]

/-- The infinite coupled configuration law, constructed from conditional refinements. -/
def infiniteClusterMeasure : Measure ((n : ℕ) → Conf n) :=
  InverseSystem.pathMeasure connectedMeasure coarse

instance infiniteClusterMeasure_probability : IsProbabilityMeasure infiniteClusterMeasure := by
  unfold infiniteClusterMeasure
  infer_instance

/-- Each level is exactly critical percolation conditioned on connection. -/
theorem infiniteClusterMeasure_map_eval (n : ℕ) :
    infiniteClusterMeasure.map (fun path => path n) = connectedMeasure n :=
  InverseSystem.pathMeasure_map_eval connectedMeasure coarse measurable_coarse
    connectedMeasure_map_coarse n

/-- All levels satisfy the substitution coarse-graining relation simultaneously. -/
theorem infiniteClusterMeasure_bonded :
    ∀ᵐ path ∂infiniteClusterMeasure, ∀ n, coarse n (path (n + 1)) = path n :=
  InverseSystem.pathMeasure_all_bonded connectedMeasure coarse measurable_coarse
    connectedMeasure_map_coarse

/-- Each level of the infinite reduced tree is read from the corresponding cluster. -/
def infiniteReducedTree (n : ℕ) (path : (n : ℕ) → Conf n) : RConf n := Phi n (path n)

lemma measurable_infiniteReducedTree (n : ℕ) : Measurable (infiniteReducedTree n) :=
  (measurable_Phi n).comp (measurable_pi_apply n)

/-- The reduction of the infinite cluster has exactly the prescribed substitution-tree laws. -/
theorem infiniteReducedTree_law (n : ℕ) :
    infiniteClusterMeasure.map (infiniteReducedTree n) =
      rMeasure (pdiamond pc) (pseries pc) n := by
  have critical_mass_ne_zero : ENNReal.ofReal pc ≠ 0 := by simp [pc_pos]
  change infiniteClusterMeasure.map (Phi n ∘ fun path => path n) = _
  rw [← Measure.map_map (measurable_Phi n) (measurable_pi_apply n),
    infiniteClusterMeasure_map_eval, connectedMeasure, ProbabilityTheory.cond,
    confMeasure_connSet, Measure.map_smul, Phi_pushforward, smul_smul,
    ENNReal.inv_mul_cancel critical_mass_ne_zero ENNReal.ofReal_ne_top, one_smul]

/-- The reduced trees retain the same ancestor choices at every level. -/
theorem infiniteReducedTree_bonded :
    ∀ᵐ path ∂infiniteClusterMeasure, ∀ n,
      rtrunc n (infiniteReducedTree (n + 1) path) = infiniteReducedTree n path := by
  filter_upwards [infiniteClusterMeasure_bonded] with path path_bonded
  intro n
  rw [infiniteReducedTree, rtrunc_Phi, path_bonded n]
  rfl

/-- The quenched critical resistance exponent on the constructed nested process. -/
theorem infinite_critical_cluster_exponent :
    ∃ α : ℝ, 0 < α ∧ α ≤ Real.log 2 ∧
      Real.log ((14 - 4 * Real.sqrt 5) / 3) ≤ α ∧
      (∀ᵐ path ∂infiniteClusterMeasure, Tendsto
        (fun n => Real.log ((res n (path n)).toReal) / n) atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log (E1 (pdiamond pc) (pseries pc) n) / n)
        atTop (𝓝 α) := by
  apply critical_cluster_exponent infiniteClusterMeasure (fun n path => path n)
    (fun n => measurable_pi_apply n)
  intro n
  rw [infiniteClusterMeasure_map_eval, connectedMeasure, setOf_res_ne_top]
  rfl

/-- An infinite critical configuration whose levels are compatible at every sample point. -/
def NestedCluster := InverseSystem.compatiblePaths coarse

instance instNestedClusterMeasurableSpace : MeasurableSpace NestedCluster :=
  inferInstanceAs (MeasurableSpace (InverseSystem.compatiblePaths coarse))

/-- The probability measure on the actual inverse limit of connected critical clusters. -/
def nestedClusterMeasure : Measure NestedCluster :=
  InverseSystem.compatibleMeasure connectedMeasure coarse

instance nestedClusterMeasure_probability : IsProbabilityMeasure nestedClusterMeasure :=
  InverseSystem.compatibleMeasure_probability connectedMeasure coarse measurable_coarse
    connectedMeasure_map_coarse

/-- The level configuration of a nested cluster. -/
def nestedConfiguration (n : ℕ) (cluster : NestedCluster) : Conf n := cluster.val n

lemma measurable_nestedConfiguration (n : ℕ) : Measurable (nestedConfiguration n) :=
  (measurable_pi_apply n).comp measurable_subtype_coe

/-- Coarse compatibility holds everywhere on the inverse-limit sample space. -/
theorem nestedConfiguration_bonded (cluster : NestedCluster) (n : ℕ) :
    coarse n (nestedConfiguration (n + 1) cluster) = nestedConfiguration n cluster :=
  cluster.property n

/-- The actual inverse-limit configurations have the critical conditioned laws. -/
theorem nestedConfiguration_law (n : ℕ) :
    nestedClusterMeasure.map (nestedConfiguration n) = connectedMeasure n :=
  InverseSystem.compatibleMeasure_map_eval connectedMeasure coarse measurable_coarse
    connectedMeasure_map_coarse n

/-- The critical quenched exponent for genuine compatible infinite cluster configurations. -/
theorem nested_critical_cluster_exponent :
    ∃ α : ℝ, 0 < α ∧ α ≤ Real.log 2 ∧
      Real.log ((14 - 4 * Real.sqrt 5) / 3) ≤ α ∧
      (∀ᵐ cluster ∂nestedClusterMeasure, Tendsto
        (fun n => Real.log ((res n (nestedConfiguration n cluster)).toReal) / n)
        atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log (E1 (pdiamond pc) (pseries pc) n) / n)
        atTop (𝓝 α) := by
  apply critical_cluster_exponent nestedClusterMeasure nestedConfiguration
    measurable_nestedConfiguration
  intro n
  rw [nestedConfiguration_law, connectedMeasure, setOf_res_ne_top]
  rfl

/-- The full critical statement also includes the expected logarithmic resistance. -/
theorem nested_critical_cluster_full_exponent :
    ∃ α : ℝ, 0 < α ∧ α ≤ Real.log 2 ∧
      Real.log ((14 - 4 * Real.sqrt 5) / 3) ≤ α ∧
      (∀ᵐ cluster ∂nestedClusterMeasure, Tendsto
        (fun n => Real.log ((res n (nestedConfiguration n cluster)).toReal) / n)
        atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log (E1 (pdiamond pc) (pseries pc) n) / n)
        atTop (𝓝 α) ∧
      Tendsto (fun n =>
        (∫ cluster, Real.log ((res n (nestedConfiguration n cluster)).toReal)
          ∂nestedClusterMeasure) / n) atTop (𝓝 α) := by
  obtain ⟨α, exponent_positive, exponent_upper, exponent_lower,
    quenched_limit, annealed_limit⟩ := nested_critical_cluster_exponent
  obtain ⟨β, _, _, second_annealed_limit, mean_log_limit⟩ :=
    quenched_exponent_all_parameters_of_marginal_laws
      (pdiamond_pos pc_pos pc_lt_one) (pdiamond_lt_one pc_pos pc_lt_one)
      pseries_pc_nonneg pseries_add_pdiamond_pc nestedClusterMeasure
      (fun n cluster => (res n (nestedConfiguration n cluster)).toReal)
      (fun n => ENNReal.measurable_toReal.comp
        ((measurable_res n).comp (measurable_nestedConfiguration n)))
      (fun n => by
        change nestedClusterMeasure.map
          ((ENNReal.toReal ∘ res n) ∘ nestedConfiguration n) = _
        rw [← Measure.map_map (ENNReal.measurable_toReal.comp (measurable_res n))
          (measurable_nestedConfiguration n), nestedConfiguration_law,
          connectedMeasure]
        simpa only [setOf_res_ne_top, connSet] using cluster_resistance_law n)
  have exponent_equality : β = α :=
    tendsto_nhds_unique second_annealed_limit annealed_limit
  subst β
  exact ⟨α, exponent_positive, exponent_upper, exponent_lower,
    quenched_limit, annealed_limit, mean_log_limit⟩

/-- Actual critical-cluster resistance has the reduced resistance law at each depth. -/
theorem nestedCluster_resistance_law (n : ℕ) :
    nestedClusterMeasure.map
      (fun cluster => (res n (nestedConfiguration n cluster)).toReal) =
        lawMeasure (pdiamond pc) (pseries pc) n := by
  change nestedClusterMeasure.map
    ((ENNReal.toReal ∘ res n) ∘ nestedConfiguration n) = _
  rw [← Measure.map_map (ENNReal.measurable_toReal.comp (measurable_res n))
    (measurable_nestedConfiguration n), nestedConfiguration_law, connectedMeasure]
  simpa only [setOf_res_ne_top, connSet] using cluster_resistance_law n

/-- The annealed mean in the capstone is the actual cluster's expected resistance. -/
theorem nestedCluster_mean_resistance (n : ℕ) :
    (∫ cluster, (res n (nestedConfiguration n cluster)).toReal ∂nestedClusterMeasure) =
      E1 (pdiamond pc) (pseries pc) n := by
  have measurable_actual_resistance :
      Measurable (fun cluster => (res n (nestedConfiguration n cluster)).toReal) :=
    ENNReal.measurable_toReal.comp
      ((measurable_res n).comp (measurable_nestedConfiguration n))
  unfold E1
  rw [← nestedCluster_resistance_law n,
    integral_map measurable_actual_resistance.aemeasurable (by fun_prop)]

/-- The full quenched and annealed theorem entirely in the original cluster observables. -/
theorem nested_critical_cluster_original_observables :
    ∃ α : ℝ, 0 < α ∧ α ≤ Real.log 2 ∧
      Real.log ((14 - 4 * Real.sqrt 5) / 3) ≤ α ∧
      (∀ᵐ cluster ∂nestedClusterMeasure, Tendsto
        (fun n => Real.log ((res n (nestedConfiguration n cluster)).toReal) / n)
        atTop (𝓝 α)) ∧
      Tendsto (fun n =>
        Real.log (∫ cluster, (res n (nestedConfiguration n cluster)).toReal
          ∂nestedClusterMeasure) / n) atTop (𝓝 α) ∧
      Tendsto (fun n =>
        (∫ cluster, Real.log ((res n (nestedConfiguration n cluster)).toReal)
          ∂nestedClusterMeasure) / n) atTop (𝓝 α) := by
  simpa only [nestedCluster_mean_resistance] using nested_critical_cluster_full_exponent

end
end Cluster
