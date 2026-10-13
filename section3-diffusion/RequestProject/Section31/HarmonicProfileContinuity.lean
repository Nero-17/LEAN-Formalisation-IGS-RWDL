import RequestProject.Section31.HarmonicProfileStability

/-! Actual finite unit harmonic profiles are continuous under convergence of
positive colour resistances. The minimizers and Poincaré bounds are constructed
from graph connectivity, rather than supplied as hypotheses. -/

namespace EIGS.Network

open IGS.Sec31 Filter Topology

variable {K : ℕ} (network : Network K)

noncomputable def unitPotentialProfile (resistances : Fin K → ℝ)
    (positive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (sourceNeSink : source ≠ sink) : network.V → ℝ :=
  Classical.choose (network.exists_minimum_potential_energy_eq_inverse_effRes resistances positive
    connected source sink sourceNeSink)

theorem unitPotentialProfile_source (resistances : Fin K → ℝ)
    (positive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (sourceNeSink : source ≠ sink) :
    network.unitPotentialProfile resistances positive connected source sink sourceNeSink source = 1 :=
  (Classical.choose_spec (network.exists_minimum_potential_energy_eq_inverse_effRes resistances positive
    connected source sink sourceNeSink)).1

theorem unitPotentialProfile_sink (resistances : Fin K → ℝ)
    (positive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (sourceNeSink : source ≠ sink) :
    network.unitPotentialProfile resistances positive connected source sink sourceNeSink sink = 0 :=
  (Classical.choose_spec (network.exists_minimum_potential_energy_eq_inverse_effRes resistances positive
    connected source sink sourceNeSink)).2.1

theorem unitPotentialProfile_minimal (resistances : Fin K → ℝ)
    (positive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (sourceNeSink : source ≠ sink)
    (competitor : network.V → ℝ) (competitorSource : competitor source = 1)
    (competitorSink : competitor sink = 0) :
    (network.potentialNetwork resistances positive).energy
        (network.unitPotentialProfile resistances positive connected source sink sourceNeSink) ≤
      (network.potentialNetwork resistances positive).energy competitor :=
  (Classical.choose_spec (network.exists_minimum_potential_energy_eq_inverse_effRes resistances positive
    connected source sink sourceNeSink)).2.2.1 competitor competitorSource competitorSink

theorem unitPotentialProfile_tendsto
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (resistanceSequence : ℕ → Fin K → ℝ)
    (sequencePositive : ∀ index colour, 0 < resistanceSequence index colour)
    (resistancesConverge : ∀ colour,
      Tendsto (fun index => resistanceSequence index colour) atTop (𝓝 (resistances colour)))
    (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (sourceNeSink : source ≠ sink) (vertex : network.V) :
    Tendsto (fun index => network.unitPotentialProfile (resistanceSequence index) (sequencePositive index)
        connected source sink sourceNeSink vertex) atTop
      (𝓝 (network.unitPotentialProfile resistances positive connected source sink sourceNeSink vertex)) := by
  obtain ⟨stabilityConstant, stabilityNonnegative, stabilityBound⟩ :=
    network.exists_unit_potential_profile_stability_bound resistances positive connected source sink
      (network.unitPotentialProfile resistances positive connected source sink sourceNeSink)
      (network.unitPotentialProfile_source resistances positive connected source sink sourceNeSink)
      (network.unitPotentialProfile_sink resistances positive connected source sink sourceNeSink)
      (network.unitPotentialProfile_minimal resistances positive connected source sink sourceNeSink)
  have conductanceDifferenceLimit : Tendsto (fun index =>
      ∑ edge, |(resistanceSequence index (network.color edge))⁻¹ -
        (resistances (network.color edge))⁻¹|) atTop (𝓝 0) := by
    have coordinateDifferenceLimit : ∀ edge : network.E, Tendsto (fun index =>
        |(resistanceSequence index (network.color edge))⁻¹ -
          (resistances (network.color edge))⁻¹|) atTop (𝓝 0) := by
      intro edge
      have limitConductanceConstant : Tendsto (fun _ : ℕ => (resistances (network.color edge))⁻¹)
          atTop (𝓝 ((resistances (network.color edge))⁻¹)) := tendsto_const_nhds
      simpa only [sub_self, abs_zero] using
        (((resistancesConverge (network.color edge)).inv₀ (ne_of_gt (positive _))).sub limitConductanceConstant).abs
    simpa only [Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun edge _ => coordinateDifferenceLimit edge)
  have rootLimit : Tendsto (fun index => Real.sqrt (stabilityConstant *
      ∑ edge, |(resistanceSequence index (network.color edge))⁻¹ -
        (resistances (network.color edge))⁻¹|)) atTop (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (conductanceDifferenceLimit.const_mul stabilityConstant)
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [Real.norm_eq_abs] using squeeze_zero
    (fun index => abs_nonneg (network.unitPotentialProfile (resistanceSequence index) (sequencePositive index)
      connected source sink sourceNeSink vertex -
      network.unitPotentialProfile resistances positive connected source sink sourceNeSink vertex))
    (fun index => by
      have squareBound := stabilityBound (resistanceSequence index) (sequencePositive index)
        (network.unitPotentialProfile (resistanceSequence index) (sequencePositive index) connected source sink sourceNeSink)
        (network.unitPotentialProfile_source (resistanceSequence index) (sequencePositive index) connected source sink sourceNeSink)
        (network.unitPotentialProfile_sink (resistanceSequence index) (sequencePositive index) connected source sink sourceNeSink)
        (network.unitPotentialProfile_minimal (resistanceSequence index) (sequencePositive index) connected source sink sourceNeSink)
        vertex
      exact Real.abs_le_sqrt squareBound)
    rootLimit

theorem unitPotentialProfile_tendsto_function
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (resistanceSequence : ℕ → Fin K → ℝ)
    (sequencePositive : ∀ index colour, 0 < resistanceSequence index colour)
    (resistancesConverge : ∀ colour,
      Tendsto (fun index => resistanceSequence index colour) atTop (𝓝 (resistances colour)))
    (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (sourceNeSink : source ≠ sink) :
    Tendsto (fun index => network.unitPotentialProfile (resistanceSequence index) (sequencePositive index)
        connected source sink sourceNeSink) atTop
      (𝓝 (network.unitPotentialProfile resistances positive connected source sink sourceNeSink)) := by
  apply tendsto_pi_nhds.2
  intro vertex
  exact network.unitPotentialProfile_tendsto resistances positive resistanceSequence sequencePositive
    resistancesConverge connected source sink sourceNeSink vertex

theorem unitPotentialProfile_norm_sub_tendsto_zero
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (resistanceSequence : ℕ → Fin K → ℝ)
    (sequencePositive : ∀ index colour, 0 < resistanceSequence index colour)
    (resistancesConverge : ∀ colour,
      Tendsto (fun index => resistanceSequence index colour) atTop (𝓝 (resistances colour)))
    (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (sourceNeSink : source ≠ sink) :
    Tendsto (fun index => ‖network.unitPotentialProfile (resistanceSequence index) (sequencePositive index)
        connected source sink sourceNeSink -
      network.unitPotentialProfile resistances positive connected source sink sourceNeSink‖) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.1
    (network.unitPotentialProfile_tendsto_function resistances positive resistanceSequence sequencePositive
      resistancesConverge connected source sink sourceNeSink)

end EIGS.Network
