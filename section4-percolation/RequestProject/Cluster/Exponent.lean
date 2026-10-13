import RequestProject.Cluster.Prop42
import RequestProject.Cluster.Tree
import RequestProject.Reduced.MarginalLimit
import RequestProject.Reduced.Positivity

/-!
# Resistance exponents under arbitrary couplings of critical clusters

The marginal law theorem now supplies the hypotheses of the quenched exponent
theorem directly. The only probabilistic input is that the configurations have the
critical conditioned percolation laws. No independence across levels, moment bounds,
submultiplicativity, or convergence conclusion is assumed.

This is a transfer theorem for an existing coupling; it does not construct an
infinite projective-limit configuration space.
-/

namespace Cluster

open MeasureTheory Filter Topology Reduced

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every coupling of the critical clusters conditioned on connection has the same
strictly positive quenched resistance exponent as the reduced process. -/
theorem critical_cluster_exponent
    (P : Measure Ω) [IsProbabilityMeasure P]
    (configuration : (n : ℕ) → Ω → Conf n)
    (hmeas : ∀ n, Measurable (configuration n))
    (hlaw : ∀ n, P.map (configuration n) =
      ProbabilityTheory.cond (confMeasure pc n) {c | res n c ≠ ⊤}) :
    ∃ α : ℝ, 0 < α ∧ α ≤ Real.log 2 ∧
      Real.log ((14 - 4 * Real.sqrt 5) / 3) ≤ α ∧
      (∀ᵐ ω ∂P, Tendsto
        (fun n => Real.log ((res n (configuration n ω)).toReal) / n) atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log (E1 (pdiamond pc) (pseries pc) n) / n)
        atTop (𝓝 α) := by
  obtain ⟨α, hamem, hannealed, hlower, hpos⟩ := alpha_pc_pos
  have hthird : (pdiamond pc) ^ 2 ≤ 1 / 3 := by
    have hnonneg : 0 ≤ pdiamond pc := pdiamond_pc_nonneg
    have hhalf : pdiamond pc < 1 / 2 := pdiamond_pc_lt_half
    nlinarith
  refine ⟨α, hpos, hamem.2, hlower, ?_, hannealed⟩
  apply quenched_ae_of_marginal_laws pdiamond_pc_nonneg pseries_pc_nonneg
    pseries_add_pdiamond_pc hthird P
    (fun n ω => (res n (configuration n ω)).toReal)
    (fun n => ENNReal.measurable_toReal.comp ((measurable_res n).comp (hmeas n)))
    ?_ hannealed
  intro n
  change P.map ((ENNReal.toReal ∘ res n) ∘ configuration n) = _
  rw [← Measure.map_map (ENNReal.measurable_toReal.comp (measurable_res n))
    (hmeas n), hlaw n]
  exact cluster_resistance_law n

/-- The same exponent theorem applies to any realization of the substitution trees
with the prescribed depth-wise laws, including correlated realizations. -/
theorem reduced_tree_exponent
    {pd ps : ℝ} (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    (hthird : pd ^ 2 ≤ 1 / 3)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (tree : (n : ℕ) → Ω → RConf n)
    (hmeas : ∀ n, Measurable (tree n))
    (hlaw : ∀ n, P.map (tree n) = rMeasure pd ps n) :
    ∃ α, α ∈ Set.Icc (0 : ℝ) (Real.log 2) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => Real.log (Rres n (tree n ω)) / n)
        atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log (E1 pd ps n) / n) atTop (𝓝 α) := by
  apply reduced_quenched_exponent_of_marginal_laws hpd hps hsum hthird P
    (fun n ω => Rres n (tree n ω))
    (fun n => (Measurable.of_discrete : Measurable (Rres n)).comp (hmeas n))
  intro n
  change P.map (Rres n ∘ tree n) = _
  rw [← Measure.map_map (Measurable.of_discrete : Measurable (Rres n)) (hmeas n),
    hlaw n]
  exact rMeasure_map_Rres hpd hps hsum n

end

end Cluster
