import RequestProject.Section31.TraceEnergyClosability
import RequestProject.Section31.TraceEnergyPythagoras

/-! Pointwise convergence controls each actual finite edge sum. Combined with
energy Cauchy convergence, it controls the constructed extended trace energy.
The identification of L2 convergence with pointwise convergence is separate. -/

namespace IGS.Sec31

open Filter Topology
open scoped BigOperators

variable {Vertex : Type*}

theorem FiniteNetwork.energy_tendsto_zero_of_pointwise (network : FiniteNetwork Vertex)
    (sequence : ℕ → Vertex → ℝ)
    (pointwiseZero : ∀ vertex, Tendsto (fun index => sequence index vertex) atTop (nhds 0)) :
    Tendsto (fun index => network.energy (sequence index)) atTop (nhds 0) := by
  have convergence : Tendsto sequence atTop (nhds (0 : Vertex → ℝ)) :=
    tendsto_pi_nhds.2 pointwiseZero
  have energyConvergence := network.energy_continuous_pointwise.continuousAt.tendsto.comp convergence
  simpa only [FiniteNetwork.energy, Pi.zero_apply, sub_self, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero] using energyConvergence

theorem finite_trace_energy_difference_bound (networks : ℕ → FiniteNetwork Vertex)
    (level : ℕ) (first second : traceEnergyDomain networks) :
    (networks level).energy first ≤
      2 * traceEnergyValue networks (first - second) + 2 * (networks level).energy second := by
  have differenceBound := (networks level).energy_add_le
    ((first : Vertex → ℝ) - (second : Vertex → ℝ)) second
  rw [sub_add_cancel] at differenceBound
  exact differenceBound.trans (add_le_add
    (mul_le_mul_of_nonneg_left (finite_energy_le_traceEnergyValue networks (first - second) level)
      (by norm_num : (0 : ℝ) ≤ 2)) le_rfl)

theorem traceEnergyValue_difference_bound (networks : ℕ → FiniteNetwork Vertex)
    (first second : traceEnergyDomain networks) :
    traceEnergyValue networks first ≤
      2 * traceEnergyValue networks (first - second) + 2 * traceEnergyValue networks second := by
  rw [traceEnergyValue_eq_iSup]
  apply ciSup_le
  intro level
  exact (finite_trace_energy_difference_bound networks level first second).trans
    (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (finite_energy_le_traceEnergyValue networks second level)
        (by norm_num : (0 : ℝ) ≤ 2)))

theorem traceEnergyValue_bounded_of_energy_cauchy (networks : ℕ → FiniteNetwork Vertex)
    (sequence : ℕ → traceEnergyDomain networks)
    (energyCauchy : ∀ tolerance > 0, ∃ threshold, ∀ first ≥ threshold, ∀ second ≥ threshold,
      traceEnergyValue networks (sequence first - sequence second) < tolerance) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ index, traceEnergyValue networks (sequence index) ≤ bound := by
  have nonnegative : ∀ index, 0 ≤ traceEnergyValue networks (sequence index) :=
    fun _ => ENNReal.toReal_nonneg
  obtain ⟨threshold, differenceSmall⟩ := energyCauchy 1 (by norm_num)
  refine ⟨2 + 2 * traceEnergyValue networks (sequence threshold) +
    ∑ index ∈ Finset.range threshold, traceEnergyValue networks (sequence index), ?_, ?_⟩
  · have prefixNonnegative : 0 ≤ ∑ index ∈ Finset.range threshold,
        traceEnergyValue networks (sequence index) :=
      Finset.sum_nonneg (fun index _ => nonnegative index)
    linarith [nonnegative threshold]
  · intro index
    by_cases afterThreshold : threshold ≤ index
    · have differenceBound := traceEnergyValue_difference_bound networks (sequence index) (sequence threshold)
      have small := differenceSmall index afterThreshold threshold le_rfl
      have prefixNonnegative : 0 ≤ ∑ earlier ∈ Finset.range threshold,
          traceEnergyValue networks (sequence earlier) :=
        Finset.sum_nonneg (fun earlier _ => nonnegative earlier)
      linarith
    · have prefixBound : traceEnergyValue networks (sequence index) ≤
          ∑ earlier ∈ Finset.range threshold, traceEnergyValue networks (sequence earlier) :=
        Finset.single_le_sum (fun earlier _ => nonnegative earlier)
          (Finset.mem_range.mpr (Nat.lt_of_not_ge afterThreshold))
      linarith [nonnegative threshold]

theorem traceEnergyValue_tendsto_zero_of_energy_cauchy_pointwise
    (networks : ℕ → FiniteNetwork Vertex)
    (energyIncreasing : ∀ values : Vertex → ℝ, Monotone (fun level => (networks level).energy values))
    (sequence : ℕ → traceEnergyDomain networks)
    (energyCauchy : ∀ tolerance > 0, ∃ threshold, ∀ first ≥ threshold, ∀ second ≥ threshold,
      traceEnergyValue networks (sequence first - sequence second) < tolerance)
    (pointwiseZero : ∀ vertex, Tendsto (fun index => (sequence index).val vertex) atTop (nhds 0)) :
    Tendsto (fun index => traceEnergyValue networks (sequence index)) atTop (nhds 0) := by
  apply energy_tendsto_zero_of_cauchy_and_finite_traces
    (traceEnergyValue networks) (fun level values => (networks level).energy values)
    (fun _ => ENNReal.toReal_nonneg)
    (finite_energy_tendsto_traceEnergyValue networks energyIncreasing)
    (finite_trace_energy_difference_bound networks) sequence energyCauchy
  intro level
  exact (networks level).energy_tendsto_zero_of_pointwise
    (fun index => (sequence index).val) pointwiseZero

end IGS.Sec31

#print axioms IGS.Sec31.FiniteNetwork.energy_tendsto_zero_of_pointwise
#print axioms IGS.Sec31.finite_trace_energy_difference_bound
#print axioms IGS.Sec31.traceEnergyValue_difference_bound
#print axioms IGS.Sec31.traceEnergyValue_bounded_of_energy_cauchy
#print axioms IGS.Sec31.traceEnergyValue_tendsto_zero_of_energy_cauchy_pointwise
