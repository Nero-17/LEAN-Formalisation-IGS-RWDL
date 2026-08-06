import RequestProject.Reduced.JointSpace
import RequestProject.Reduced.Positivity

/-!
# Headline theorem at the critical point

This file assembles the three results of Subsection 4.1 — the concrete quenched exponent
(`reduced_quenched_exponent_concrete`), the unconditional annealed exponent
(`reduced_annealed_exponent`) and the positivity of the critical exponent (`alpha_pc_pos`) —
into a single statement, instantiated at the critical parameter `p_c`.

Write `P := jointMeasure (pdiamond pc) (pseries pc)` for the product law on `ℝ^ℕ` and
`R_n := proj n` for the `n`-th coordinate.  The theorem `reduced_exponent_critical` asserts:
there is a deterministic constant `α` with `0 < α ≤ log 2` and
`log ((14 − 4√5)/3) ≤ α` such that

* `P`-almost surely `(1/n) log R_n → α` (the quenched exponent exists a.s.), and
* `(1/n) log E[R_n] → α` (the annealed exponent equals it),

i.e. at `p_c` the quenched exponent exists almost surely, equals the annealed exponent,
and is strictly positive.
-/

namespace Reduced

open MeasureTheory Real Filter Topology Set

noncomputable section

/-- At the critical parameter the diamond probability satisfies `pd² ≤ 1/3`, since
`pdiamond pc = √5 − 2 < 1/2` is nonnegative and `(1/2)² = 1/4 < 1/3`.  (In fact
`pdiamond pc ^ 2 = (√5 − 2)² = 9 − 4√5 < 1/3`.) -/
lemma pdiamond_pc_sq_le_third : (pdiamond pc) ^ 2 ≤ 1 / 3 := by
  have h0 : 0 ≤ pdiamond pc := pdiamond_nonneg pc_pos pc_lt_one
  have h1 : pdiamond pc < 1 / 2 := pdiamond_pc_lt_half
  nlinarith [h0, h1]

/-- **Headline theorem at the critical point.**

With `P := jointMeasure (pdiamond pc) (pseries pc)` the product law on `ℝ^ℕ` and
`R_n := proj n` the coordinate projections, there exists a deterministic constant `α`
with `0 < α`, `α ≤ log 2` and `log ((14 − 4√5)/3) ≤ α` such that

* `P`-almost surely `(1/n) log R_n → α`, and
* `(1/n) log E[R_n] → α`.

In words: at `p_c` the quenched exponent exists almost surely, equals the annealed exponent,
and is strictly positive.  This merges `reduced_quenched_exponent_concrete`,
`reduced_annealed_exponent` and `alpha_pc_pos`. -/
theorem reduced_exponent_critical :
    ∃ α : ℝ, 0 < α ∧ α ≤ Real.log 2 ∧ Real.log ((14 - 4 * Real.sqrt 5) / 3) ≤ α ∧
      (∀ᵐ ω ∂(jointMeasure (pdiamond pc) (pseries pc)),
        Tendsto (fun n => Real.log (proj n ω) / n) atTop (𝓝 α)) ∧
      Tendsto (fun n => Real.log (E1 (pdiamond pc) (pseries pc) n) / n) atTop (𝓝 α) := by
  have hpd : 0 ≤ pdiamond pc := pdiamond_nonneg pc_pos pc_lt_one
  have hps : 0 ≤ pseries pc := pseries_nonneg pc_pos pc_lt_one
  have hsum : pseries pc + pdiamond pc = 1 := pseries_add_pdiamond pc_pos pc_lt_one
  -- Quenched exponent (a.s.) and annealed exponent for the concrete model at `p_c`.
  obtain ⟨α, hαmem, hαae, hαannealed⟩ :=
    reduced_quenched_exponent_concrete hpd hps hsum pdiamond_pc_sq_le_third
  -- Positivity / lower bound of the annealed exponent at `p_c`.
  obtain ⟨β, _, hβannealed, hβlow, hβpos⟩ := alpha_pc_pos
  -- The two exponents are limits of the *same* sequence, hence equal.
  have hαβ : α = β := tendsto_nhds_unique hαannealed hβannealed
  subst hαβ
  exact ⟨α, hβpos, hαmem.2, hβlow, hαae, hαannealed⟩

end

end Reduced
