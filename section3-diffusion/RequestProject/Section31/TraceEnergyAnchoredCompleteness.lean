import RequestProject.Section31.TraceEnergyPointwiseClosability
import Mathlib.Topology.MetricSpace.Cauchy

/-! Anchored completeness for the constructed finite-trace energy domain.
The evaluation bound is a finite-network interface, not a completeness
assumption. The limit is constructed pointwise and its energy is recovered
from continuity of each finite edge sum. -/

namespace IGS.Sec31

open Filter Topology
noncomputable section

variable {Vertex : Type*}

theorem traceEnergyDomain_mem_of_pointwise_bounded_energy
    (networks : ℕ → FiniteNetwork Vertex)
    (sequence : ℕ → traceEnergyDomain networks) (limit : Vertex → ℝ)
    (pointwise : ∀ vertex, Tendsto (fun index => (sequence index).val vertex)
      atTop (𝓝 (limit vertex)))
    (bound : ℝ) (bounded : ∀ᶠ index in atTop, traceEnergyValue networks (sequence index) ≤ bound) :
    limit ∈ traceEnergyDomain networks ∧
      (extendedTraceEnergy networks limit).toReal ≤ bound := by
  have finite : limit ∈ traceEnergyDomain networks := by
    refine ⟨bound, fun level => ?_⟩
    apply le_of_tendsto ((networks level).energy_continuous_pointwise.continuousAt.tendsto.comp
      (tendsto_pi_nhds.2 pointwise))
    filter_upwards [bounded] with index after
    exact (finite_energy_le_traceEnergyValue networks (sequence index) level).trans after
  refine ⟨finite, ?_⟩
  change traceEnergyValue networks ⟨limit, finite⟩ ≤ bound
  rw [traceEnergyValue_eq_iSup]
  apply ciSup_le
  intro level
  apply le_of_tendsto ((networks level).energy_continuous_pointwise.continuousAt.tendsto.comp
    (tendsto_pi_nhds.2 pointwise))
  filter_upwards [bounded] with index after
  exact (finite_energy_le_traceEnergyValue networks (sequence index) level).trans after

theorem traceEnergy_anchored_cauchy_pointwise
    (networks : ℕ → FiniteNetwork Vertex) (anchor : Vertex)
    (evaluation : ∀ vertex, ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ values : traceEnergyDomain networks,
        (values.val vertex) ^ 2 ≤ coefficient *
          (traceEnergyValue networks values + (values.val anchor) ^ 2))
    (sequence : ℕ → traceEnergyDomain networks)
    (cauchy : ∀ tolerance > 0, ∃ threshold : ℕ,
      ∀ first ≥ threshold, ∀ second ≥ threshold,
        traceEnergyValue networks (sequence first - sequence second) +
          ((sequence first).val anchor - (sequence second).val anchor) ^ 2 < tolerance)
    (vertex : Vertex) : CauchySeq (fun index => (sequence index).val vertex) := by
  obtain ⟨coefficient, positive, control⟩ := evaluation vertex
  apply Metric.cauchySeq_iff.mpr
  intro tolerance tolerancePositive
  obtain ⟨threshold, small⟩ := cauchy (tolerance ^ 2 / coefficient) (by positivity)
  refine ⟨threshold, fun first firstAfter second secondAfter => ?_⟩
  have controlled := control (sequence first - sequence second)
  have multiplied := mul_lt_mul_of_pos_left (small first firstAfter second secondAfter) positive
  have cancellation : coefficient * (tolerance ^ 2 / coefficient) = tolerance ^ 2 := by
    field_simp
  rw [cancellation] at multiplied
  change ((sequence first).val vertex - (sequence second).val vertex) ^ 2 ≤
    coefficient * (traceEnergyValue networks (sequence first - sequence second) +
      ((sequence first).val anchor - (sequence second).val anchor) ^ 2) at controlled
  rw [Real.dist_eq]
  nlinarith [sq_abs ((sequence first).val vertex - (sequence second).val vertex),
    abs_nonneg ((sequence first).val vertex - (sequence second).val vertex)]

theorem exists_traceEnergy_anchored_cauchy_limit
    (networks : ℕ → FiniteNetwork Vertex) (anchor : Vertex)
    (evaluation : ∀ vertex, ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ values : traceEnergyDomain networks,
        (values.val vertex) ^ 2 ≤ coefficient *
          (traceEnergyValue networks values + (values.val anchor) ^ 2))
    (sequence : ℕ → traceEnergyDomain networks)
    (cauchy : ∀ tolerance > 0, ∃ threshold : ℕ,
      ∀ first ≥ threshold, ∀ second ≥ threshold,
        traceEnergyValue networks (sequence first - sequence second) +
          ((sequence first).val anchor - (sequence second).val anchor) ^ 2 < tolerance) :
    ∃ limit : traceEnergyDomain networks,
      (∀ vertex, Tendsto (fun index => (sequence index).val vertex) atTop (𝓝 (limit.val vertex))) ∧
      ∀ tolerance > 0, ∀ᶠ index in atTop,
        traceEnergyValue networks (sequence index - limit) +
          ((sequence index).val anchor - limit.val anchor) ^ 2 ≤ tolerance := by
  have existence : ∀ vertex, ∃ value : ℝ,
      Tendsto (fun index => (sequence index).val vertex) atTop (𝓝 value) := by
    intro vertex
    exact cauchySeq_tendsto_of_complete
      (traceEnergy_anchored_cauchy_pointwise networks anchor evaluation sequence cauchy vertex)
  choose limit convergence using existence
  have energyCauchy : ∀ tolerance > 0, ∃ threshold,
      ∀ first ≥ threshold, ∀ second ≥ threshold,
        traceEnergyValue networks (sequence first - sequence second) < tolerance := by
    intro tolerance positive
    obtain ⟨threshold, small⟩ := cauchy tolerance positive
    exact ⟨threshold, fun first firstAfter second secondAfter =>
      lt_of_le_of_lt (le_add_of_nonneg_right (sq_nonneg _))
        (small first firstAfter second secondAfter)⟩
  obtain ⟨bound, _, bounded⟩ := traceEnergyValue_bounded_of_energy_cauchy networks sequence energyCauchy
  have finite := (traceEnergyDomain_mem_of_pointwise_bounded_energy networks sequence limit
    convergence bound (Filter.Eventually.of_forall bounded)).1
  refine ⟨⟨limit, finite⟩, convergence, ?_⟩
  intro tolerance positive
  obtain ⟨threshold, small⟩ := cauchy tolerance positive
  filter_upwards [eventually_ge_atTop threshold] with index after
  have traceBounds : ∀ level,
      (networks level).energy ((sequence index).val - limit) +
        ((sequence index).val anchor - limit anchor) ^ 2 ≤ tolerance := by
    intro level
    apply le_of_tendsto (((networks level).energy_continuous_pointwise.continuousAt.tendsto.comp
      (tendsto_pi_nhds.2 (fun vertex => tendsto_const_nhds.sub (convergence vertex)))).add
      ((tendsto_const_nhds.sub (convergence anchor)).pow 2))
    filter_upwards [eventually_ge_atTop threshold] with second secondAfter
    have finiteBound := finite_energy_le_traceEnergyValue networks (sequence index - sequence second) level
    exact (add_le_add_right finiteBound _).trans (small index after second secondAfter).le
  have energyBound : traceEnergyValue networks (sequence index - ⟨limit, finite⟩) ≤
      tolerance - ((sequence index).val anchor - limit anchor) ^ 2 := by
    rw [traceEnergyValue_eq_iSup]
    apply ciSup_le
    intro level
    have bound := traceBounds level
    change (networks level).energy ((sequence index).val - limit) ≤ _
    linarith
  change traceEnergyValue networks (sequence index - ⟨limit, finite⟩) +
    ((sequence index).val anchor - limit anchor) ^ 2 ≤ tolerance
  linarith

end
end IGS.Sec31

#print axioms IGS.Sec31.traceEnergyDomain_mem_of_pointwise_bounded_energy
#print axioms IGS.Sec31.traceEnergy_anchored_cauchy_pointwise
#print axioms IGS.Sec31.exists_traceEnergy_anchored_cauchy_limit
