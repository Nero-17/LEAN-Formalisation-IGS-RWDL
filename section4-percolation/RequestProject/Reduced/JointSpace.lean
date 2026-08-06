import RequestProject.Reduced.Capstone
import RequestProject.Reduced.Cases23
import Mathlib.Probability.ProductMeasure

/-!
# A single probability space carrying the whole reduced-resistance sequence

The abstract theorem `reduced_quenched_exponent` (in `Limit.lean`) is stated for an arbitrary
process `R : ℕ → Ω → ℝ` on an arbitrary probability space.  This file *realises the whole
sequence on one concrete probability space*, as described in Subsection 4.1:

* the sample space is `Ω := ℝ^ℕ` (`SamplePath`);
* the law is the infinite product `P := ⨂ₙ μ_n` of the level-`n` marginal laws
  `μ_n = lawMeasure pd ps n` (`jointMeasure`);
* the `n`-th resistance is the `n`-th coordinate projection `R_n := π_n` (`proj`).

We prove the **marginal identity** `(R_n)_* P = μ_n` (`jointMeasure_map_proj`).  Consequently the
marginal facts already established for `μ_n` — the bounds `1 ≤ R_n ≤ 2^n`, the uniform
product-moment bound `E[R_n]·E[1/R_n] ≤ 11/5` (`E1Einv_le`) and the submultiplicativity
`E[R_{a+b}] ≤ E[R_a]·E[R_b]` (`E1_submultiplicative`) — supply exactly the hypotheses
`hge`, `hle`, `hM`, `hsub` of `reduced_quenched_exponent`.

To feed the abstract theorem (which asks for *everywhere* bounds `1 ≤ R_n ω ≤ 2^n`) we pass
through the clamped process `Rclamp n ω := max 1 (min (2^n) (ω n))`, which agrees with `π_n`
almost surely (since `μ_n` is supported on `[1, 2^n]`) and has identical integrals.  Transferring
the almost-sure convergence back from `Rclamp` to `π_n` yields, for the concrete model, that
`P`-almost surely `(1/n) log R_n → α` as `n → ∞`.
-/

namespace Reduced

open MeasureTheory Measure Real Filter Topology Set

noncomputable section

variable {pd ps : ℝ}

/-- The sample space `Ω = ℝ^ℕ`. -/
abbrev SamplePath : Type := ℕ → ℝ

/-- The `n`-th resistance `R_n := π_n`, the `n`-th coordinate projection on `ℝ^ℕ`. -/
def proj (n : ℕ) : (ℕ → ℝ) → ℝ := fun ω => ω n

/-- The joint law `P = ⨂ₙ μ_n` on `ℝ^ℕ`: the infinite product of the level-`n` marginal laws. -/
def jointMeasure (pd ps : ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (lawMeasure pd ps)

lemma measurable_proj (n : ℕ) : Measurable (proj n) := measurable_pi_apply n

/-- The level-`n` marginal laws form a family of probability measures. -/
lemma isProb_family (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) :
    ∀ n, IsProbabilityMeasure (lawMeasure pd ps n) :=
  fun n => isProb_lawMeasure hpd hps hsum n

/-- `P` is a probability measure. -/
lemma isProb_jointMeasure (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) :
    IsProbabilityMeasure (jointMeasure pd ps) := by
  haveI : ∀ n, IsProbabilityMeasure (lawMeasure pd ps n) := isProb_family hpd hps hsum
  exact inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (lawMeasure pd ps)))

/-- **Marginal identity.** The pushforward of the coordinate projection `R_n = π_n` under the
product law `P` is exactly the level-`n` marginal law `μ_n`. -/
lemma jointMeasure_map_proj (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    (jointMeasure pd ps).map (proj n) = lawMeasure pd ps n := by
  haveI : ∀ n, IsProbabilityMeasure (lawMeasure pd ps n) := isProb_family hpd hps hsum
  exact Measure.infinitePi_map_eval (lawMeasure pd ps) n

/-- Almost surely, the projection `R_n` lands in the support `[1, 2^n]` of its law. -/
lemma proj_mem_ae (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    ∀ᵐ ω ∂(jointMeasure pd ps), proj n ω ∈ Set.Icc (1 : ℝ) (2 ^ n) := by
  have hsupp := lawMeasure_support hpd hps hsum n
  rw [← jointMeasure_map_proj hpd hps hsum n] at hsupp
  exact (ae_map_iff (measurable_proj n).aemeasurable measurableSet_Icc).mp hsupp

/-! ## The clamped process, agreeing with `π_n` almost surely -/

/-- The clamped process: `R'_n ω = max 1 (min (2^n) (ω n))`.  It satisfies the *everywhere*
bounds `1 ≤ R'_n ≤ 2^n` and agrees with the projection `π_n` almost surely. -/
def Rclamp (n : ℕ) (ω : ℕ → ℝ) : ℝ := max 1 (min (2 ^ n) (ω n))

lemma measurable_Rclamp (n : ℕ) : Measurable (Rclamp n) := by
  unfold Rclamp; fun_prop

lemma Rclamp_ge (n : ℕ) (ω : ℕ → ℝ) : 1 ≤ Rclamp n ω := le_max_left _ _

lemma Rclamp_le (n : ℕ) (ω : ℕ → ℝ) : Rclamp n ω ≤ 2 ^ n := by
  unfold Rclamp
  exact max_le (one_le_pow₀ (by norm_num)) (min_le_left _ _)

lemma Rclamp_ae_eq_proj (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    Rclamp n =ᵐ[jointMeasure pd ps] proj n := by
  filter_upwards [proj_mem_ae hpd hps hsum n] with ω hω
  obtain ⟨h1, h2⟩ := hω
  show max 1 (min (2 ^ n) (proj n ω)) = proj n ω
  rw [min_eq_right h2, max_eq_right h1]

/-! ## Integrals of the clamped process match the marginal moments -/

/-- `E_P[R'_n] = E[R_n] = E1`. -/
lemma integral_Rclamp (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    ∫ ω, Rclamp n ω ∂(jointMeasure pd ps) = E1 pd ps n := by
  rw [integral_congr_ae (Rclamp_ae_eq_proj hpd hps hsum n)]
  unfold E1
  rw [← jointMeasure_map_proj hpd hps hsum n,
    integral_map (measurable_proj n).aemeasurable (by fun_prop)]

/-- `E_P[1/R'_n] = E[1/R_n] = Einv`. -/
lemma integral_Rclamp_inv (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    ∫ ω, (Rclamp n ω)⁻¹ ∂(jointMeasure pd ps) = Einv pd ps n := by
  have h : (fun ω => (Rclamp n ω)⁻¹) =ᵐ[jointMeasure pd ps] (fun ω => (proj n ω)⁻¹) := by
    filter_upwards [Rclamp_ae_eq_proj hpd hps hsum n] with ω hω; rw [hω]
  rw [integral_congr_ae h]
  unfold Einv
  rw [← jointMeasure_map_proj hpd hps hsum n,
    integral_map (measurable_proj n).aemeasurable (by fun_prop)]

/-! ## The concrete quenched exponent on the joint space -/

/-- **Reduced quenched exponent for the concrete model.**

Realising the whole sequence on `Ω = ℝ^ℕ` with the product law `P = ⨂ₙ μ_n` and
`R_n = π_n` the coordinate projections, the marginal facts established for `μ_n`
(bounds `1 ≤ R_n ≤ 2^n`, product-moment bound `E[R_n]·E[1/R_n] ≤ 11/5` and
submultiplicativity `E[R_{a+b}] ≤ E[R_a]·E[R_b]`) yield a deterministic constant
`α ∈ [0, log 2]` such that `P`-almost surely `(1/n) log R_n → α` as `n → ∞`,
*and at the same time* the annealed exponent `(1/n) log E[R_n] → α`.  Thus the quenched
exponent exists almost surely and equals the annealed exponent, for the concrete model.

The result is stated in the regime `pd² ≤ 1/3` (i.e. `pd ≤ 1/√3`, which contains the
critical parameter `p_c`), where the uniform product-moment bound `E1Einv_le_of_sq` holds. -/
theorem reduced_quenched_exponent_concrete
    (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (hthird : pd ^ 2 ≤ 1 / 3) :
    ∃ α, α ∈ Set.Icc (0 : ℝ) (Real.log 2) ∧
      (∀ᵐ ω ∂(jointMeasure pd ps),
        Tendsto (fun n => Real.log (proj n ω) / n) atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log (E1 pd ps n) / n) atTop (𝓝 α) := by
  haveI : IsProbabilityMeasure (jointMeasure pd ps) := isProb_jointMeasure hpd hps hsum
  -- Apply the abstract theorem to the clamped process `Rclamp`.
  obtain ⟨α, hαmem, hαae, hαannealed, _⟩ :=
    reduced_quenched_exponent (jointMeasure pd ps) Rclamp
      (fun n => measurable_Rclamp n) (fun n ω => Rclamp_ge n ω) (fun n ω => Rclamp_le n ω)
      (11 / 5)
      (fun n => by
        rw [integral_Rclamp hpd hps hsum n, integral_Rclamp_inv hpd hps hsum n]
        exact E1Einv_le_of_sq hpd hps hsum hthird n)
      (fun a b => by
        rw [integral_Rclamp hpd hps hsum (a + b), integral_Rclamp hpd hps hsum a,
          integral_Rclamp hpd hps hsum b]
        exact E1_submultiplicative hpd hps hsum a b)
  refine ⟨α, hαmem, ?_, ?_⟩
  · -- Quenched part: transfer the convergence from `Rclamp` to the projection,
    -- using a.s. equality for every `n`.
    have hall : ∀ᵐ ω ∂(jointMeasure pd ps), ∀ n, Rclamp n ω = proj n ω := by
      rw [MeasureTheory.ae_all_iff]
      exact fun n => Rclamp_ae_eq_proj hpd hps hsum n
    filter_upwards [hαae, hall] with ω hω heq
    have : (fun n => Real.log (proj n ω) / n) = (fun n => Real.log (Rclamp n ω) / n) := by
      funext n; rw [heq n]
    rw [this]
    exact hω
  · -- Annealed part: rewrite `∫ R'_n dP = E1 pd ps n` (= `E[R_n]`) via `integral_Rclamp`.
    have : (fun n => Real.log (∫ ω, Rclamp n ω ∂(jointMeasure pd ps)) / n)
        = (fun n => Real.log (E1 pd ps n) / n) := by
      funext n; rw [integral_Rclamp hpd hps hsum n]
    rwa [this] at hαannealed

end

end Reduced
