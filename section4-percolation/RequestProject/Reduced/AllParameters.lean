import RequestProject.Reduced.MarginalLimit

/-!
# Unconditional moment bounds in all parameter regimes

The increasing-concave order already proved for the resistance recursion
implies monotonicity of the means. This discharges the remaining `hmono`
input in the third regime of the uniform product-moment estimate.
-/

namespace Reduced

open MeasureTheory Filter Topology Set

noncomputable section

variable {pd ps : ℝ}

/-- The unit leaf law is below every resistance law in increasing-concave order. -/
lemma unitLaw_icv_lawMeasure
    (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    IcvLEon 1 (Measure.dirac 1) (lawMeasure pd ps n) := by
  intro test_function _ monotone_test continuous_test
  rw [integral_dirac]
  haveI := isProb_lawMeasure hpd hps hsum n
  have constant_integral :
      (∫ _ : ℝ, test_function 1 ∂lawMeasure pd ps n) = test_function 1 := by simp
  rw [← constant_integral]
  apply integral_mono_ae (integrable_const _)
    (integrable_of_continuousOn (GoodM_lawMeasure hpd hps hsum n) continuous_test)
  filter_upwards [lawMeasure_support hpd hps hsum n] with resistance resistance_bounds
  exact monotone_test (show (1 : ℝ) ∈ Set.Ici (1 : ℝ) by simp)
    resistance_bounds.1 resistance_bounds.1

/-- Refinement increases the annealed resistance, for every admissible parameter. -/
theorem E1_monotone_step
    (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    E1 pd ps n ≤ E1 pd ps (n + 1) := by
  have unit_law_good : GoodM 1 (Measure.dirac (1 : ℝ)) := GoodM_dirac le_rfl
  have lifted_order := genLaw_icv hpd hps hsum unit_law_good
    (GoodM_lawMeasure hpd hps hsum 1) (unitLaw_icv_lawMeasure hpd hps hsum 1) n
  have mean_order := mean_mono_of_icv lifted_order
  have refined_law : genLaw pd ps (lawMeasure pd ps 1) n = lawMeasure pd ps (n + 1) := by
    rw [lawMeasure_eq_genLaw (n + 1), genLaw_comp, ← lawMeasure_eq_genLaw 1]
  rw [refined_law, ← lawMeasure_eq_genLaw n] at mean_order
  exact mean_order

/-- The full paper product-moment lemma has no monotonicity hypothesis left. -/
theorem uniform_product_all_parameters
    (hpd0 : 0 < pd) (hpd1 : pd < 1) (hps : 0 ≤ ps) (hsum : ps + pd = 1) :
    ∃ bound : ℝ, ∀ n, E1 pd ps n * Einv pd ps n ≤ bound :=
  uniform_product_lemma45 hpd0 hpd1 hps hsum
    (E1_monotone_step hpd0.le hps hsum)

/-- The full quenched theorem, with both annealed exponents, under any coupling
of the actual resistance laws and throughout the paper's parameter interval. -/
theorem quenched_exponent_all_parameters_of_marginal_laws
    (hpd0 : 0 < pd) (hpd1 : pd < 1) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    {Ω : Type*} [MeasurableSpace Ω]
    (probability : Measure Ω) [IsProbabilityMeasure probability]
    (resistance : ℕ → Ω → ℝ)
    (measurable_resistance : ∀ n, Measurable (resistance n))
    (resistance_law : ∀ n, probability.map (resistance n) = lawMeasure pd ps n) :
    ∃ α : ℝ, α ∈ Set.Icc 0 (Real.log 2) ∧
      (∀ᵐ sample ∂probability, Tendsto
        (fun n => Real.log (resistance n sample) / n) atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log (E1 pd ps n) / n) atTop (𝓝 α) ∧
      Tendsto (fun n => (∫ sample, Real.log (resistance n sample) ∂probability) / n)
        atTop (𝓝 α) := by
  let boundedResistance : ℕ → Ω → ℝ :=
    fun n sample => max 1 (min (2 ^ n) (resistance n sample))
  have bounded_measurable : ∀ n, Measurable (boundedResistance n) :=
    fun n => measurable_const.max (measurable_const.min (measurable_resistance n))
  have bounded_lower : ∀ n sample, 1 ≤ boundedResistance n sample :=
    fun _ _ => le_max_left _ _
  have bounded_upper : ∀ n sample, boundedResistance n sample ≤ 2 ^ n := by
    intro n sample
    exact max_le (one_le_pow₀ (by norm_num)) (min_le_left _ _)
  have bounded_eq : ∀ n, boundedResistance n =ᵐ[probability] resistance n := by
    intro n
    have support := lawMeasure_support hpd0.le hps hsum n
    rw [← resistance_law n] at support
    have sample_support :=
      (ae_map_iff (measurable_resistance n).aemeasurable measurableSet_Icc).mp support
    filter_upwards [sample_support] with sample sample_bounds
    exact (show max 1 (min (2 ^ n) (resistance n sample)) = resistance n sample by
      rw [min_eq_right sample_bounds.2, max_eq_right sample_bounds.1])
  have mean_eq : ∀ n, (∫ sample, boundedResistance n sample ∂probability) =
      E1 pd ps n := by
    intro n
    rw [integral_congr_ae (bounded_eq n)]
    unfold E1
    rw [← resistance_law n,
      integral_map (measurable_resistance n).aemeasurable (by fun_prop)]
  have inverse_mean_eq : ∀ n,
      (∫ sample, (boundedResistance n sample)⁻¹ ∂probability) = Einv pd ps n := by
    intro n
    have inverse_eq : (fun sample => (boundedResistance n sample)⁻¹) =ᵐ[probability]
        (fun sample => (resistance n sample)⁻¹) := by
      filter_upwards [bounded_eq n] with sample equality
      rw [equality]
    rw [integral_congr_ae inverse_eq]
    unfold Einv
    rw [← resistance_law n,
      integral_map (measurable_resistance n).aemeasurable (by fun_prop)]
  have log_mean_eq : ∀ n, meanLog probability boundedResistance n =
      ∫ sample, Real.log (resistance n sample) ∂probability := by
    intro n
    apply integral_congr_ae
    filter_upwards [bounded_eq n] with sample equality
    rw [equality]
  obtain ⟨moment_bound, uniform_bound⟩ :=
    uniform_product_all_parameters hpd0 hpd1 hps hsum
  obtain ⟨α, exponent_bounds, quenched_limit, annealed_limit, logarithmic_limit⟩ :=
    reduced_quenched_exponent probability boundedResistance bounded_measurable bounded_lower
      bounded_upper moment_bound
      (fun n => by rw [mean_eq n, inverse_mean_eq n]; exact uniform_bound n)
      (fun n m => by
        rw [mean_eq (n + m), mean_eq n, mean_eq m]
        exact E1_submultiplicative hpd0.le hps hsum n m)
  refine ⟨α, exponent_bounds, ?_, ?_, ?_⟩
  · have simultaneous_eq : ∀ᵐ sample ∂probability,
        ∀ n, boundedResistance n sample = resistance n sample := ae_all_iff.mpr bounded_eq
    filter_upwards [quenched_limit, simultaneous_eq] with sample sample_limit equality
    simpa only [equality] using sample_limit
  · simpa only [mean_eq] using annealed_limit
  · simpa only [log_mean_eq] using logarithmic_limit

end
end Reduced
