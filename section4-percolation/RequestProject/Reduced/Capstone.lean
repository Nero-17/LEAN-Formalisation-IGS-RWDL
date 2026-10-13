import RequestProject.Reduced.Limit
import RequestProject.Reduced.Submultiplicative

/-!
# Unconditional annealed exponent for the concrete reduced–resistance process

This file ties together the two structural facts that were previously *assumptions* of the
abstract capstone `reduced_quenched_exponent` in `Limit.lean`:

* the **uniform product–moment bound** `E[R n] · E[1/R n] ≤ 11/5` (`uniform_product`,
  `Moments.lean`), and
* the **submultiplicativity of the mean** `E[R_{a+b}] ≤ E[R_a] · E[R_b]`
  (`E1_submultiplicative`, `Submultiplicative.lean`), established via the concavity / Jensen
  argument on the random series–parallel network.

Using submultiplicativity, we discharge Fekete's lemma directly for the concrete mean
`E1 pd ps`, obtaining the existence of the **annealed exponent**
`α = lim (log E[R n]) / n ∈ [0, log 2]` with *no* extra hypotheses beyond the parameter
constraints.  This is the analytic content of the "annealed exponent" lemma of Subsection 4.1,
now fully unconditional for the modelled process.
-/

namespace Reduced

open MeasureTheory Measure Real Set Filter Topology

noncomputable section

variable {pd ps : ℝ}

/-
The mean reduced resistance is bounded above by `2 ^ n` (the deterministic series bound).
-/
lemma E1_le_pow (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) (n : ℕ) :
    E1 pd ps n ≤ 2 ^ n := by
  refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
  refine' fun x => 2 ^ n;
  · filter_upwards [ Reduced.lawMeasure_support hpd hps hsum n ] with x hx using hx.1.trans' ( by norm_num );
  · have := Reduced.prob_law hpd hps hsum n; aesop;
  · filter_upwards [ Reduced.lawMeasure_support hpd hps hsum n ] with x hx using hx.2;
  · have := Reduced.prob_law hpd hps hsum n; aesop;

/-- **Unconditional annealed exponent for the reduced–resistance process.**

Combining the deterministic bounds `1 ≤ E[R n] ≤ 2 ^ n` with the submultiplicativity
`E[R_{a+b}] ≤ E[R_a] · E[R_b]` (the concavity / Jensen argument, `E1_submultiplicative`),
Fekete's lemma yields a deterministic constant `α ∈ [0, log 2]` with
`(log E[R n]) / n → α`.  No hypotheses other than the parameter constraints are needed:
the self-similarity input is now a theorem, not an assumption. -/
theorem reduced_annealed_exponent (hpd : 0 ≤ pd) (hps : 0 ≤ ps) (hsum : ps + pd = 1) :
    ∃ α, α ∈ Set.Icc (0 : ℝ) (Real.log 2) ∧
      Tendsto (fun n => Real.log (E1 pd ps n) / n) atTop (𝓝 α) :=
  fekete_exponent (E1 pd ps)
    (fun n => E1_ge_one hpd hps hsum n)
    (fun n => E1_le_pow hpd hps hsum n)
    (fun a b => E1_submultiplicative hpd hps hsum a b)

end

end Reduced