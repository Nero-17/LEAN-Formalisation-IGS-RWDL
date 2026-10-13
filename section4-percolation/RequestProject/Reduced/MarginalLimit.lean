import RequestProject.Reduced.Capstone
import RequestProject.Reduced.Cases23

/-!
# The quenched exponent depends only on the one-level laws

The independent product realization in `JointSpace` is not the substitution-tree
coupling of the reduced networks. This file closes that distinction: every measurable
process with the proved reduced-resistance marginal laws has the same almost-sure
exponent. No independence between levels is required. The proof transfers the support
and moment facts through the marginal maps and applies the Borel--Cantelli theorem
already proved in `Limit`.
-/

namespace Reduced

open MeasureTheory Filter Topology Set

noncomputable section

variable {pd ps : ℝ} {Ω : Type*} [MeasurableSpace Ω]

/-- The quenched and annealed exponents coincide for **any coupling** of the
reduced-resistance laws. In particular, the probability space need not be a product
space and the resistances at distinct levels need not be independent. -/
theorem reduced_quenched_exponent_of_marginal_laws
    (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    (hthird : pd ^ 2 ≤ 1 / 3)
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℕ → Ω → ℝ)
    (hmeas : ∀ n, Measurable (R n))
    (hmarginal : ∀ n, P.map (R n) = lawMeasure pd ps n) :
    ∃ α, α ∈ Set.Icc (0 : ℝ) (Real.log 2) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => Real.log (R n ω) / n) atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log (E1 pd ps n) / n) atTop (𝓝 α) := by
  let boundedResistance : ℕ → Ω → ℝ := fun n ω => max 1 (min (2 ^ n) (R n ω))
  have hboundedMeas : ∀ n, Measurable (boundedResistance n) := by
    intro n
    exact measurable_const.max (measurable_const.min (hmeas n))
  have hboundedGe : ∀ n ω, 1 ≤ boundedResistance n ω :=
    fun n ω => le_max_left _ _
  have hboundedLe : ∀ n ω, boundedResistance n ω ≤ 2 ^ n := by
    intro n ω
    exact max_le (one_le_pow₀ (by norm_num)) (min_le_left _ _)
  have hboundedEq : ∀ n, boundedResistance n =ᵐ[P] R n := by
    intro n
    have hsupp := lawMeasure_support hpd hps hsum n
    rw [← hmarginal n] at hsupp
    have hsupp' := (ae_map_iff (hmeas n).aemeasurable measurableSet_Icc).mp hsupp
    filter_upwards [hsupp'] with ω hω
    exact (show max 1 (min (2 ^ n) (R n ω)) = R n ω by
      rw [min_eq_right hω.2, max_eq_right hω.1])
  have hmean : ∀ n, (∫ ω, boundedResistance n ω ∂P) = E1 pd ps n := by
    intro n
    rw [integral_congr_ae (hboundedEq n)]
    unfold E1
    rw [← hmarginal n, integral_map (hmeas n).aemeasurable (by fun_prop)]
  have hinv : ∀ n, (∫ ω, (boundedResistance n ω)⁻¹ ∂P) = Einv pd ps n := by
    intro n
    have heq : (fun ω => (boundedResistance n ω)⁻¹) =ᵐ[P]
        (fun ω => (R n ω)⁻¹) := by
      filter_upwards [hboundedEq n] with ω hω
      rw [hω]
    rw [integral_congr_ae heq]
    unfold Einv
    rw [← hmarginal n, integral_map (hmeas n).aemeasurable (by fun_prop)]
  obtain ⟨α, hamem, haae, haannealed, _⟩ :=
    reduced_quenched_exponent P boundedResistance hboundedMeas hboundedGe hboundedLe
      (11 / 5)
      (fun n => by
        rw [hmean n, hinv n]
        exact E1Einv_le_of_sq hpd hps hsum hthird n)
      (fun a b => by
        rw [hmean (a + b), hmean a, hmean b]
        exact E1_submultiplicative hpd hps hsum a b)
  refine ⟨α, hamem, ?_, ?_⟩
  · have hall : ∀ᵐ ω ∂P, ∀ n, boundedResistance n ω = R n ω :=
      ae_all_iff.mpr hboundedEq
    filter_upwards [haae, hall] with ω hω heq
    simpa only [heq] using hω
  · simpa only [hmean] using haannealed

/-- The exponent is fixed by the marginal laws: once the annealed limit is known,
it is the almost-sure limit under every coupling of those laws. -/
theorem quenched_ae_of_marginal_laws
    (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    (hthird : pd ^ 2 ≤ 1 / 3)
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℕ → Ω → ℝ)
    (hmeas : ∀ n, Measurable (R n))
    (hmarginal : ∀ n, P.map (R n) = lawMeasure pd ps n)
    {α : ℝ} (hannealed :
      Tendsto (fun n => Real.log (E1 pd ps n) / n) atTop (𝓝 α)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => Real.log (R n ω) / n) atTop (𝓝 α) := by
  obtain ⟨β, _, hquenched, hlimit⟩ :=
    reduced_quenched_exponent_of_marginal_laws hpd hps hsum hthird P R hmeas hmarginal
  have heq : β = α := tendsto_nhds_unique hlimit hannealed
  simpa only [heq] using hquenched

end

end Reduced
