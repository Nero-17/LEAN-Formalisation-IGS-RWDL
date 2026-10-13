import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-! An elementary final step in a trace-energy closability argument. This
lemma does not assert that actual L2 convergence identifies the finite traces;
that substantive identification must be proved for the concrete form first. -/

namespace IGS.Sec31

open Filter Topology

theorem energy_tendsto_zero_of_cauchy_and_finite_traces
    {FunctionSpace : Type*} [Sub FunctionSpace]
    (energy : FunctionSpace → ℝ) (trace_energy : ℕ → FunctionSpace → ℝ)
    (energy_nonnegative : ∀ function, 0 ≤ energy function)
    (trace_limit : ∀ function,
      Tendsto (fun level => trace_energy level function) atTop (nhds (energy function)))
    (trace_difference_bound : ∀ level first second,
      trace_energy level first ≤ 2 * energy (first - second) + 2 * trace_energy level second)
    (sequence : ℕ → FunctionSpace)
    (energy_cauchy : ∀ tolerance > 0, ∃ threshold, ∀ first ≥ threshold, ∀ second ≥ threshold,
      energy (sequence first - sequence second) < tolerance)
    (finite_trace_zero : ∀ level,
      Tendsto (fun index => trace_energy level (sequence index)) atTop (nhds 0)) :
    Tendsto (fun index => energy (sequence index)) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro tolerance tolerance_positive
  obtain ⟨threshold, difference_small⟩ := energy_cauchy (tolerance / 4) (by positivity)
  refine ⟨threshold, fun index index_large => ?_⟩
  have trace_bound : ∀ level, trace_energy level (sequence index) ≤ tolerance / 2 := by
    intro level
    have upper_limit : Tendsto (fun later => tolerance / 2 +
        2 * trace_energy level (sequence later)) atTop (nhds (tolerance / 2)) := by
      simpa using tendsto_const_nhds.add ((finite_trace_zero level).const_mul 2)
    apply ge_of_tendsto upper_limit
    filter_upwards [eventually_ge_atTop threshold] with later later_large
    have difference_bound := trace_difference_bound level (sequence index) (sequence later)
    have difference_small := difference_small index index_large later later_large
    linarith
  have energy_bound : energy (sequence index) ≤ tolerance / 2 :=
    le_of_tendsto (trace_limit (sequence index)) (Eventually.of_forall trace_bound)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (energy_nonnegative _)]
  linarith

end IGS.Sec31

#print axioms IGS.Sec31.energy_tendsto_zero_of_cauchy_and_finite_traces
