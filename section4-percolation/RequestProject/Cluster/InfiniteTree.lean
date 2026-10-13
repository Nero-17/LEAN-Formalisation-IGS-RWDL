import RequestProject.Cluster.InverseLimit
import RequestProject.Cluster.Tree
import RequestProject.Cluster.TreeNetwork
import RequestProject.Reduced.AllParameters

/-!
# The infinite nested series/diamond replacement process

The finite tree laws are consistent under forgetting the finest generation.
The inverse-limit construction therefore realizes the actual nested process,
and the all-parameter resistance exponent theorem applies to its coordinates.
-/

namespace Cluster

open MeasureTheory ProbabilityTheory Filter Topology Reduced

noncomputable section

instance instRConfNonempty : (n : ℕ) → Nonempty (RConf n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n + 1 =>
      let _ := instRConfNonempty n
      inferInstanceAs
        (Nonempty ((RConf n × RConf n) ⊕ ((RConf n × RConf n) × (RConf n × RConf n))))

variable {pd ps : ℝ}

/-- The finite substitution trees have consistent ancestor laws. -/
theorem rMeasure_map_rtrunc
    (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    (rMeasure pd ps (n + 1)).map (rtrunc n) = rMeasure pd ps n := by
  induction n with
  | zero =>
      haveI := isProb_rMeasure hpd hps hsum 1
      rw [rtrunc, Measure.map_const, measure_univ, one_smul]
      rfl
  | succ n induction_hypothesis =>
      haveI := isProb_rMeasure hpd hps hsum n
      haveI := isProb_rMeasure hpd hps hsum (n + 1)
      have series_composition : rtrunc (n + 1) ∘ rinl (n + 1) =
          rinl n ∘ Prod.map (rtrunc n) (rtrunc n) := rfl
      have diamond_composition : rtrunc (n + 1) ∘ rinr (n + 1) =
          rinr n ∘ Prod.map (Prod.map (rtrunc n) (rtrunc n))
            (Prod.map (rtrunc n) (rtrunc n)) := rfl
      rw [rMeasure_succ pd ps (n + 1),
        Measure.map_add _ _ (Measurable.of_discrete : Measurable (rtrunc (n + 1))),
        Measure.map_smul, Measure.map_smul,
        Measure.map_map Measurable.of_discrete Measurable.of_discrete,
        Measure.map_map Measurable.of_discrete Measurable.of_discrete,
        series_composition, diamond_composition,
        ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
        ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
        rprod4,
        ← Measure.map_prod_map _ _ Measurable.of_discrete Measurable.of_discrete,
        ← Measure.map_prod_map _ _ Measurable.of_discrete Measurable.of_discrete,
        ← Measure.map_prod_map _ _ Measurable.of_discrete Measurable.of_discrete,
        induction_hypothesis, rMeasure_succ]
      rfl

/-- Infinite replacement trees whose ancestor choices agree at every depth. -/
def NestedTree := InverseSystem.compatiblePaths rtrunc

instance instNestedTreeMeasurableSpace : MeasurableSpace NestedTree :=
  inferInstanceAs (MeasurableSpace (InverseSystem.compatiblePaths rtrunc))

/-- Probability law of the actual infinite nested replacement tree. -/
def nestedTreeMeasure (pd ps : ℝ)
    (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) : Measure NestedTree := by
  letI : ∀ n, IsProbabilityMeasure (rMeasure pd ps n) :=
    fun n => isProb_rMeasure hpd hps hsum n
  exact InverseSystem.compatibleMeasure (rMeasure pd ps) rtrunc

theorem nestedTreeMeasure_probability
    (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) :
    IsProbabilityMeasure (nestedTreeMeasure pd ps hpd hps hsum) := by
  letI : ∀ n, IsProbabilityMeasure (rMeasure pd ps n) :=
    fun n => isProb_rMeasure hpd hps hsum n
  exact InverseSystem.compatibleMeasure_probability (rMeasure pd ps) rtrunc
    (fun _ => Measurable.of_discrete) (rMeasure_map_rtrunc hpd hps hsum)

def nestedTree (n : ℕ) (tree : NestedTree) : RConf n := tree.val n

lemma measurable_nestedTree (n : ℕ) : Measurable (nestedTree n) :=
  (measurable_pi_apply n).comp measurable_subtype_coe

theorem nestedTree_bonded (tree : NestedTree) (n : ℕ) :
    rtrunc n (nestedTree (n + 1) tree) = nestedTree n tree := tree.property n

/-- The infinite nested tree has exactly the independently branching finite tree laws. -/
theorem nestedTree_law
    (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    (nestedTreeMeasure pd ps hpd hps hsum).map (nestedTree n) = rMeasure pd ps n := by
  letI : ∀ n, IsProbabilityMeasure (rMeasure pd ps n) :=
    fun n => isProb_rMeasure hpd hps hsum n
  exact InverseSystem.compatibleMeasure_map_eval (rMeasure pd ps) rtrunc
    (fun _ => Measurable.of_discrete) (rMeasure_map_rtrunc hpd hps hsum) n

/-- The paper's full reduced quenched exponent theorem on the actual infinite nested tree. -/
theorem nested_tree_quenched_exponent
    (hpd0 : 0 < pd) (hpd1 : pd < 1) (hps : 0 ≤ ps) (hsum : ps + pd = 1) :
    ∃ α : ℝ, α ∈ Set.Icc 0 (Real.log 2) ∧
      (∀ᵐ tree ∂nestedTreeMeasure pd ps hpd0.le hps hsum, Tendsto
        (fun n => Real.log (Rres n (nestedTree n tree)) / n) atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log (E1 pd ps n) / n) atTop (𝓝 α) ∧
      Tendsto (fun n =>
        (∫ tree, Real.log (Rres n (nestedTree n tree))
          ∂nestedTreeMeasure pd ps hpd0.le hps hsum) / n) atTop (𝓝 α) := by
  haveI := nestedTreeMeasure_probability hpd0.le hps hsum
  apply quenched_exponent_all_parameters_of_marginal_laws hpd0 hpd1 hps hsum
    (nestedTreeMeasure pd ps hpd0.le hps hsum)
    (fun n tree => Rres n (nestedTree n tree))
    (fun n => (Measurable.of_discrete : Measurable (Rres n)).comp (measurable_nestedTree n))
  intro n
  change (nestedTreeMeasure pd ps hpd0.le hps hsum).map (Rres n ∘ nestedTree n) = _
  rw [← Measure.map_map (Measurable.of_discrete : Measurable (Rres n))
    (measurable_nestedTree n), nestedTree_law hpd0.le hps hsum,
    rMeasure_map_Rres hpd0.le hps hsum]

/-- The original paper parameter `p ∈ (0,1)` satisfies all required constraints. -/
theorem nested_tree_quenched_exponent_p {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ α : ℝ, α ∈ Set.Icc 0 (Real.log 2) ∧
      (∀ᵐ tree ∂nestedTreeMeasure (pdiamond p) (pseries p)
        (pdiamond_nonneg hp0 hp1) (pseries_nonneg hp0 hp1) (pseries_add_pdiamond hp0 hp1),
        Tendsto (fun n => Real.log (Rres n (nestedTree n tree)) / n) atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log (E1 (pdiamond p) (pseries p) n) / n) atTop (𝓝 α) ∧
      Tendsto (fun n =>
        (∫ tree, Real.log (Rres n (nestedTree n tree))
          ∂nestedTreeMeasure (pdiamond p) (pseries p)
            (pdiamond_nonneg hp0 hp1) (pseries_nonneg hp0 hp1)
            (pseries_add_pdiamond hp0 hp1)) / n) atTop (𝓝 α) :=
  nested_tree_quenched_exponent (pdiamond_pos hp0 hp1) (pdiamond_lt_one hp0 hp1)
    (pseries_nonneg hp0 hp1) (pseries_add_pdiamond hp0 hp1)

/-- The same theorem stated with the effective resistance of the actual finite networks. -/
theorem nested_network_quenched_exponent
    (hpd0 : 0 < pd) (hpd1 : pd < 1) (hps : 0 ≤ ps) (hsum : ps + pd = 1) :
    ∃ α : ℝ, α ∈ Set.Icc 0 (Real.log 2) ∧
      (∀ᵐ tree ∂nestedTreeMeasure pd ps hpd0.le hps hsum, Tendsto
        (fun n => Real.log ((treeNetwork n (nestedTree n tree)).effRes.toReal) / n)
          atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log (E1 pd ps n) / n) atTop (𝓝 α) ∧
      Tendsto (fun n =>
        (∫ tree, Real.log ((treeNetwork n (nestedTree n tree)).effRes.toReal)
          ∂nestedTreeMeasure pd ps hpd0.le hps hsum) / n) atTop (𝓝 α) := by
  simpa only [treeNetwork_toReal_effRes] using
    nested_tree_quenched_exponent hpd0 hpd1 hps hsum

end
end Cluster
