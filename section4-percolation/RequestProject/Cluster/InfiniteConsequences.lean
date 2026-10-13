import RequestProject.Cluster.NestedReduction
import RequestProject.Reduced.NoLimit
import RequestProject.Cluster.TreeBounds
import RequestProject.Reduced.OriginalParameters

/-!
# End-to-end consequences for the constructed infinite networks

The expected resistances and weak-limit statements below concern the actual
network observables on the compatible infinite probability spaces. Neither
independence across depths nor an abstract process existence hypothesis occurs.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction

noncomputable section

namespace Reduced

/-- The law-only negative limit theorem applies to any existing realization of those laws. -/
theorem no_deterministic_limit_of_resistance_laws
    {pd ps : ℝ} (diamond_positive : 0 < pd) (diamond_below_one : pd < 1)
    (series_nonnegative : 0 ≤ ps) (probability_sum : ps + pd = 1)
    {Ω : Type*} [MeasurableSpace Ω] (probability : Measure Ω)
    (resistance : ℕ → Ω → ℝ)
    (measurable_resistance : ∀ n, Measurable (resistance n))
    (resistance_law : ∀ n, probability.map (resistance n) = lawMeasure pd ps n)
    (scaling : ℝ) (scaling_positive : 0 < scaling) (constant : ℝ)
    (constant_nonnegative : 0 ≤ constant)
    (convergence : ∀ test_function : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ sample, test_function (scaling ^ n * resistance n sample)
        ∂probability) atTop (𝓝 (test_function constant))) : constant = 0 := by
  have series_positive : 0 < ps := by linarith
  have series_below_one : ps < 1 := by linarith
  apply no_deterministic_limit diamond_positive diamond_below_one
    series_positive series_below_one probability_sum scaling scaling_positive
    constant constant_nonnegative
  intro test_function
  have integral_identity (n : ℕ) :
      (∫ value, test_function value ∂zMeasure pd ps scaling n) =
        ∫ sample, test_function (scaling ^ n * resistance n sample) ∂probability := by
    unfold zMeasure
    rw [← resistance_law n, integral_map (by fun_prop)
      test_function.continuous.measurable.aestronglyMeasurable,
      integral_map (measurable_resistance n).aemeasurable (by fun_prop)]
  simpa only [integral_identity] using convergence test_function

end Reduced

namespace Cluster

open Reduced

variable {pd ps : ℝ}

theorem measurable_nested_network_resistance (n : ℕ) :
    Measurable (fun tree => (treeNetwork n (nestedTree n tree)).effRes.toReal) := by
  simpa only [treeNetwork_toReal_effRes] using
    (Measurable.of_discrete : Measurable (Rres n)).comp (measurable_nestedTree n)

/-- The actual finite electrical network resistance has the prescribed recursion law. -/
theorem nested_network_resistance_law
    (diamond_nonnegative : 0 ≤ pd) (series_nonnegative : 0 ≤ ps)
    (probability_sum : ps + pd = 1) (n : ℕ) :
    (nestedTreeMeasure pd ps diamond_nonnegative series_nonnegative probability_sum).map
      (fun tree => (treeNetwork n (nestedTree n tree)).effRes.toReal) =
        lawMeasure pd ps n := by
  change (nestedTreeMeasure pd ps diamond_nonnegative series_nonnegative probability_sum).map
    ((fun tree : RConf n => (treeNetwork n tree).effRes.toReal) ∘ nestedTree n) = _
  rw [← Measure.map_map Measurable.of_discrete (measurable_nestedTree n),
    nestedTree_law diamond_nonnegative series_nonnegative probability_sum]
  simpa only [treeNetwork_toReal_effRes] using
    rMeasure_map_Rres diamond_nonnegative series_nonnegative probability_sum n

/-- The concrete expected network resistance is the recursion's annealed mean. -/
theorem nested_network_mean_resistance
    (diamond_nonnegative : 0 ≤ pd) (series_nonnegative : 0 ≤ ps)
    (probability_sum : ps + pd = 1) (n : ℕ) :
    (∫ tree, (treeNetwork n (nestedTree n tree)).effRes.toReal
      ∂nestedTreeMeasure pd ps diamond_nonnegative series_nonnegative probability_sum) =
        E1 pd ps n := by
  unfold E1
  rw [← nested_network_resistance_law diamond_nonnegative series_nonnegative probability_sum n,
    integral_map (measurable_nested_network_resistance n).aemeasurable (by fun_prop)]

/-- The inverse moment also concerns the actual network resistance. -/
theorem nested_network_mean_inverse_resistance
    (diamond_nonnegative : 0 ≤ pd) (series_nonnegative : 0 ≤ ps)
    (probability_sum : ps + pd = 1) (n : ℕ) :
    (∫ tree, ((treeNetwork n (nestedTree n tree)).effRes.toReal)⁻¹
      ∂nestedTreeMeasure pd ps diamond_nonnegative series_nonnegative probability_sum) =
        Einv pd ps n := by
  unfold Einv
  rw [← nested_network_resistance_law diamond_nonnegative series_nonnegative probability_sum n,
    integral_map (measurable_nested_network_resistance n).aemeasurable (by fun_prop)]

/-- All deterministic bounds used in Theorem 4.6 hold at every sample point. -/
theorem nested_network_pointwise_bounds (n : ℕ) (tree : NestedTree) :
    1 ≤ (treeNetwork n (nestedTree n tree)).effRes.toReal ∧
      (treeNetwork n (nestedTree n tree)).effRes.toReal ≤ 2 ^ n := by
  simpa only [treeNetwork_toReal_effRes] using Rres_bounds n (nestedTree n tree)

/-- The uniform product-moment assumption is a theorem for this actual process. -/
theorem nested_network_uniform_product
    (diamond_positive : 0 < pd) (diamond_below_one : pd < 1)
    (series_nonnegative : 0 ≤ ps) (probability_sum : ps + pd = 1) :
    ∃ bound : ℝ, ∀ n,
      (∫ tree, (treeNetwork n (nestedTree n tree)).effRes.toReal
        ∂nestedTreeMeasure pd ps diamond_positive.le series_nonnegative probability_sum) *
      (∫ tree, ((treeNetwork n (nestedTree n tree)).effRes.toReal)⁻¹
        ∂nestedTreeMeasure pd ps diamond_positive.le series_nonnegative probability_sum) ≤
          bound := by
  simpa only [nested_network_mean_resistance, nested_network_mean_inverse_resistance] using
    uniform_product_all_parameters diamond_positive diamond_below_one
      series_nonnegative probability_sum

/-- The mean submultiplicativity assumption is a theorem for the actual networks. -/
theorem nested_network_mean_submultiplicative
    (diamond_nonnegative : 0 ≤ pd) (series_nonnegative : 0 ≤ ps)
    (probability_sum : ps + pd = 1) (first_depth second_depth : ℕ) :
    (∫ tree, (treeNetwork (first_depth + second_depth)
      (nestedTree (first_depth + second_depth) tree)).effRes.toReal
        ∂nestedTreeMeasure pd ps diamond_nonnegative series_nonnegative probability_sum) ≤
      (∫ tree, (treeNetwork first_depth (nestedTree first_depth tree)).effRes.toReal
        ∂nestedTreeMeasure pd ps diamond_nonnegative series_nonnegative probability_sum) *
      (∫ tree, (treeNetwork second_depth (nestedTree second_depth tree)).effRes.toReal
        ∂nestedTreeMeasure pd ps diamond_nonnegative series_nonnegative probability_sum) := by
  simpa only [nested_network_mean_resistance] using
    E1_submultiplicative diamond_nonnegative series_nonnegative probability_sum
      first_depth second_depth

/-- The complete all-parameter theorem uses actual network expectations throughout. -/
theorem nested_network_original_observables
    (diamond_positive : 0 < pd) (diamond_below_one : pd < 1)
    (series_nonnegative : 0 ≤ ps) (probability_sum : ps + pd = 1) :
    ∃ α : ℝ, α ∈ Set.Icc 0 (Real.log 2) ∧
      (∀ᵐ tree ∂nestedTreeMeasure pd ps diamond_positive.le series_nonnegative probability_sum,
        Tendsto (fun n => Real.log ((treeNetwork n (nestedTree n tree)).effRes.toReal) / n)
          atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log
        (∫ tree, (treeNetwork n (nestedTree n tree)).effRes.toReal
          ∂nestedTreeMeasure pd ps diamond_positive.le series_nonnegative probability_sum) / n)
            atTop (𝓝 α) ∧
      Tendsto (fun n =>
        (∫ tree, Real.log ((treeNetwork n (nestedTree n tree)).effRes.toReal)
          ∂nestedTreeMeasure pd ps diamond_positive.le series_nonnegative probability_sum) / n)
            atTop (𝓝 α) := by
  simpa only [nested_network_mean_resistance] using
    nested_network_quenched_exponent diamond_positive diamond_below_one
      series_nonnegative probability_sum

/-- Theorem 4.6 in actual network observables under only the original `p ∈ (0,1)` assumption. -/
theorem nested_network_original_observables_p {p : ℝ} (positive : 0 < p) (below_one : p < 1) :
    ∃ α : ℝ, α ∈ Set.Icc 0 (Real.log 2) ∧
      (∀ᵐ tree ∂nestedTreeMeasure (pdiamond p) (pseries p)
        (pdiamond_nonneg positive below_one) (pseries_nonneg positive below_one)
        (pseries_add_pdiamond positive below_one),
        Tendsto (fun n => Real.log ((treeNetwork n (nestedTree n tree)).effRes.toReal) / n)
          atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log
        (∫ tree, (treeNetwork n (nestedTree n tree)).effRes.toReal
          ∂nestedTreeMeasure (pdiamond p) (pseries p)
            (pdiamond_nonneg positive below_one) (pseries_nonneg positive below_one)
            (pseries_add_pdiamond positive below_one)) / n) atTop (𝓝 α) ∧
      Tendsto (fun n =>
        (∫ tree, Real.log ((treeNetwork n (nestedTree n tree)).effRes.toReal)
          ∂nestedTreeMeasure (pdiamond p) (pseries p)
            (pdiamond_nonneg positive below_one) (pseries_nonneg positive below_one)
            (pseries_add_pdiamond positive below_one)) / n) atTop (𝓝 α) :=
  nested_network_original_observables (pdiamond_pos positive below_one)
    (pdiamond_lt_one positive below_one) (pseries_nonneg positive below_one)
    (pseries_add_pdiamond positive below_one)

/-- Proposition 4.8 on the actual compatible infinite tree probability space. -/
theorem nested_network_no_deterministic_limit
    (diamond_positive : 0 < pd) (diamond_below_one : pd < 1)
    (series_nonnegative : 0 ≤ ps) (probability_sum : ps + pd = 1)
    (scaling : ℝ) (scaling_positive : 0 < scaling) (constant : ℝ)
    (constant_nonnegative : 0 ≤ constant)
    (convergence : ∀ test_function : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ tree,
        test_function (scaling ^ n * (treeNetwork n (nestedTree n tree)).effRes.toReal)
          ∂nestedTreeMeasure pd ps diamond_positive.le series_nonnegative probability_sum)
            atTop (𝓝 (test_function constant))) : constant = 0 :=
  no_deterministic_limit_of_resistance_laws diamond_positive diamond_below_one
    series_nonnegative probability_sum
    (nestedTreeMeasure pd ps diamond_positive.le series_nonnegative probability_sum)
    (fun n tree => (treeNetwork n (nestedTree n tree)).effRes.toReal)
    measurable_nested_network_resistance
    (nested_network_resistance_law diamond_positive.le series_nonnegative probability_sum)
    scaling scaling_positive constant constant_nonnegative convergence

/-- The same negative-limit conclusion for the actual critical-cluster networks. -/
theorem nested_critical_cluster_no_deterministic_limit
    (scaling : ℝ) (scaling_positive : 0 < scaling) (constant : ℝ)
    (constant_nonnegative : 0 ≤ constant)
    (convergence : ∀ test_function : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ cluster,
        test_function (scaling ^ n * (net n (nestedConfiguration n cluster)).effRes.toReal)
          ∂nestedClusterMeasure) atTop (𝓝 (test_function constant))) : constant = 0 := by
  apply no_deterministic_limit_of_resistance_laws
    (pdiamond_pos pc_pos pc_lt_one) (pdiamond_lt_one pc_pos pc_lt_one)
    pseries_pc_nonneg pseries_add_pdiamond_pc nestedClusterMeasure
    (fun n cluster => (res n (nestedConfiguration n cluster)).toReal)
    (fun n => ENNReal.measurable_toReal.comp
      ((measurable_res n).comp (measurable_nestedConfiguration n)))
    nestedCluster_resistance_law scaling scaling_positive constant constant_nonnegative
  simpa only [res] using convergence

/-- The full joint-law identity stated with the two actual network constructions. -/
theorem nested_cluster_network_process :
    nestedClusterMeasure.map
      (fun cluster n => (net n (nestedConfiguration n cluster)).effRes.toReal) =
      (nestedClusterMeasure.map nestedClusterTree).map
        (fun tree n => (treeNetwork n (nestedTree n tree)).effRes.toReal) := by
  simpa only [res, treeNetwork_toReal_effRes] using nested_cluster_resistance_process

end Cluster
end
