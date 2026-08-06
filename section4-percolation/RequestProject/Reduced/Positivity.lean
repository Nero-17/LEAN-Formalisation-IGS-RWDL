import RequestProject.Reduced.Capstone

/-!
# Positivity of the critical annealed exponent (Proposition `α(p_c) > 0`)

This file formalises the proposition of Subsection 4.1 stating that the (annealed) exponent
`α(p)` is **strictly positive at the critical parameter** `p = p_c`.

Recall (`Capstone.lean`) that the annealed exponent
`α = lim_n (log E[R_n]) / n` exists for the concrete reduced–resistance law.  The paper's
argument shows that, in the regime `p_diamond ≤ 1/2` (which contains `p_c`, where
`p_diamond = √5 − 2 < 1/2`), the mean grows geometrically:

* the diamond–mean lower bound `E[D_n] ≥ (2/3) E[R_n]` (from the relative-second-moment bound
  `E[R_n²] ≤ 2 E[R_n]²` of Case 1), and the one-step recursion
  `E[R_{n+1}] = 2 p_series E[R_n] + p_diamond E[D_n]`, give
  `E[R_{n+1}] ≥ (2 − (4/3) p_diamond) E[R_n]`;
* iterating from `E[R_0] = 1` yields `E[R_n] ≥ (2 − (4/3) p_diamond)^n`.

Hence `α ≥ log (2 − (4/3) p_diamond)`.  At `p_c` this is
`α(p_c) ≥ log ((14 − 4√5)/3) > 0`.
-/

namespace Reduced

open MeasureTheory Measure Real Set Filter Topology

noncomputable section

variable {pd ps : ℝ}

/-- `E[R_0] = 1`. -/
lemma E1_zero : E1 pd ps 0 = 1 := by
  norm_num [E1, integral_dirac]

/-
**Diamond-mean lower bound** `(2/3) E[R_n] ≤ E[D_n]` in the regime `p_diamond ≤ 1/2`.
From the relative-second-moment bound `E[R_n²] ≤ 2 E[R_n]²` and `Dmean_lower`.
-/
lemma Dmean_ge_two_thirds (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    (hhalf : pd ≤ 1 / 2) (n : ℕ) :
    (2 / 3) * E1 pd ps n ≤ Dmean pd ps n := by
  have h_ineq : 3 * Dmean pd ps n * (E2 pd ps n + (E1 pd ps n) ^ 2) ≥ 2 * E1 pd ps n * (E2 pd ps n + (E1 pd ps n) ^ 2) := by
    nlinarith [ Dmean_lower hpd hps hsum n, E2_le_two_E1sq hpd hps hsum hhalf n, E1_ge_one hpd hps hsum n ];
  nlinarith [ show 0 < E2 pd ps n + E1 pd ps n ^ 2 from add_pos_of_nonneg_of_pos
      (MeasureTheory.integral_nonneg fun x => by positivity)
      (sq_pos_of_pos (by linarith [E1_ge_one hpd hps hsum n])) ]

/-
**One-step geometric growth** of the mean: `E[R_{n+1}] ≥ (2 − (4/3) p_diamond) E[R_n]`.
-/
lemma E1_succ_ge (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    (hhalf : pd ≤ 1 / 2) (n : ℕ) :
    (2 - (4 / 3) * pd) * E1 pd ps n ≤ E1 pd ps (n + 1) := by
  rw [ E1_succ hpd hps hsum n ];
  convert add_le_add_left ( mul_le_mul_of_nonneg_left ( Dmean_ge_two_thirds hpd hps hsum hhalf n ) hpd ) ( 2 * ps * E1 pd ps n ) using 1 ; rw [ ← eq_sub_iff_add_eq' ] at hsum ; subst_vars ; ring;
  ring

/-
The growth factor `2 − (4/3) p_diamond` is positive (indeed `≥ 4/3`) for `p_diamond ≤ 1/2`.
-/
lemma growth_factor_pos (hhalf : pd ≤ 1 / 2) : 0 < 2 - (4 / 3) * pd := by
  grind

/-
**Geometric lower bound** `(2 − (4/3) p_diamond)^n ≤ E[R_n]` by iteration.
-/
lemma E1_ge_geom (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    (hhalf : pd ≤ 1 / 2) (n : ℕ) :
    (2 - (4 / 3) * pd) ^ n ≤ E1 pd ps n := by
  induction' n with n ih <;> norm_num [ pow_succ' ] at *;
  · exact E1_zero.ge;
  · exact le_trans ( mul_le_mul_of_nonneg_left ih ( by linarith ) ) ( by linarith [ E1_succ_ge hpd hps hsum hhalf n ] )

/-
**The annealed exponent dominates** `log (2 − (4/3) p_diamond)`.
-/
theorem annealed_exponent_ge_log (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1)
    (hhalf : pd ≤ 1 / 2) {α : ℝ}
    (hα : Tendsto (fun n => Real.log (E1 pd ps n) / n) atTop (𝓝 α)) :
    Real.log (2 - (4 / 3) * pd) ≤ α := by
  have h_log_c_le_α : ∀ n ≥ 1, Real.log (2 - (4 / 3) * pd) ≤ Real.log (E1 pd ps n) / n := by
    intros n hn
    have h_log_c_le_α : Real.log ((2 - (4 / 3) * pd) ^ n) ≤ Real.log (E1 pd ps n) := by
      exact Real.log_le_log ( pow_pos ( by linarith ) _ ) ( E1_ge_geom hpd hps hsum hhalf n );
    rw [ le_div_iff₀ ( by positivity ) ] ; rw [ Real.log_pow ] at h_log_c_le_α ; linarith;
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hα ( Filter.eventually_atTop.mpr ⟨ 1, fun n hn => h_log_c_le_α n hn ⟩ )

/-- At the critical parameter, `2 − (4/3) p_diamond = (14 − 4√5)/3`. -/
lemma growth_factor_pc : 2 - (4 / 3) * pdiamond pc = (14 - 4 * Real.sqrt 5) / 3 := by
  rw [pdiamond_pc]; ring

/-- `(14 − 4√5)/3 > 1`. -/
lemma critical_growth_gt_one : 1 < (14 - 4 * Real.sqrt 5) / 3 := by
  have h : Real.sqrt 5 < 2.75 := by
    have : (2.75 : ℝ) = Real.sqrt (2.75 ^ 2) := by
      rw [Real.sqrt_sq (by norm_num)]
    rw [this]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- **Proposition (positivity of the critical exponent).**

At the critical parameter `p_c`, the annealed exponent `α = lim_n (log E[R_n])/n` exists,
lies in `[0, log 2]`, is bounded below by `log ((14 − 4√5)/3)`, and is in particular
**strictly positive**. -/
theorem alpha_pc_pos :
    ∃ α, α ∈ Set.Icc (0 : ℝ) (Real.log 2) ∧
      Tendsto (fun n => Real.log (E1 (pdiamond pc) (pseries pc) n) / n) atTop (𝓝 α) ∧
      Real.log ((14 - 4 * Real.sqrt 5) / 3) ≤ α ∧ 0 < α := by
  have hpd : 0 ≤ pdiamond pc := pdiamond_nonneg pc_pos pc_lt_one
  have hps : 0 ≤ pseries pc := pseries_nonneg pc_pos pc_lt_one
  have hsum : pseries pc + pdiamond pc = 1 := pseries_add_pdiamond pc_pos pc_lt_one
  have hhalf : pdiamond pc ≤ 1 / 2 := le_of_lt pdiamond_pc_lt_half
  obtain ⟨α, hαmem, hαtend⟩ := reduced_annealed_exponent hpd hps hsum
  have hlow : Real.log (2 - (4 / 3) * pdiamond pc) ≤ α :=
    annealed_exponent_ge_log hpd hps hsum hhalf hαtend
  rw [growth_factor_pc] at hlow
  refine ⟨α, hαmem, hαtend, hlow, ?_⟩
  have hpos : 0 < Real.log ((14 - 4 * Real.sqrt 5) / 3) :=
    Real.log_pos critical_growth_gt_one
  linarith

end

end Reduced