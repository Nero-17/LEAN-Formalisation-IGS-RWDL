import RequestProject.Section31.EIGSVertexMassLimits

/-! Joint actual edge and vertex-count asymptotics under the original rules. -/

namespace EIGS

open Filter Topology
open scoped BigOperators Classical

noncomputable section

variable {K : ℕ}

theorem eigs_vertex_edge_normalized_limits (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ (rate : ℝ) (amplitude : Fin K → ℝ) (vertexFactor : ℝ),
      1 < rate ∧ (∀ colour, 0 < amplitude colour) ∧ 0 < vertexFactor ∧
      (∀ initialColour, Tendsto (fun level =>
        (totalEdges {system.toRuleData with ι := initialColour} level : ℝ) / rate ^ level)
        atTop (𝓝 (amplitude initialColour))) ∧
      ∀ initialColour, Tendsto (fun level =>
        (Fintype.card (XiVtx {system with initCol := initialColour} level) : ℝ) / rate ^ level)
        atTop (𝓝 (vertexFactor * amplitude initialColour)) := by
  obtain ⟨rate, reference, amplitude, ratePositive, referencePositive,
    referenceNormalized, amplitudePositive, colourLimits⟩ :=
      descendant_colour_count_normalized_limits system ruleConnected distancePositive
  have edgeLimits := fun initialColour => totalEdges_normalized_limit_of_colour_limit
    {system.toRuleData with ι := initialColour} referenceNormalized (colourLimits initialColour)
  let mass : XiMassParameters system :=
    { rate := rate
      amplitude := amplitude
      rate_positive := ratePositive
      amplitude_positive := amplitudePositive
      eigenpair := mass_amplitude_eigenpair_of_descendant_limits system.toRuleData ratePositive edgeLimits
      descendant_fraction_converges := descendant_fraction_limit_of_normalized_counts system.toRuleData
        ratePositive amplitudePositive edgeLimits }
  have rateGreaterThanOne : 1 < rate :=
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      (mass.rate_ge_two system ruleConnected plantingNonadjacent)
  have interiorPositive : ∀ colour, 0 < (xiRuleInteriorCount system colour : ℝ) := by
    intro colour
    letI := rule_interior_nonempty system ruleConnected plantingNonadjacent colour
    change 0 < (Fintype.card {vertex : (system.rule colour).V //
      vertex ≠ system.plantPlus colour ∧ vertex ≠ system.plantMinus colour} : ℝ)
    exact_mod_cast Fintype.card_pos
  have weightedInteriorPositive : 0 < ∑ colour, reference colour * (xiRuleInteriorCount system colour : ℝ) :=
    Finset.sum_pos (fun colour _ => mul_pos (referencePositive colour) (interiorPositive colour))
      ⟨system.initCol, Finset.mem_univ _⟩
  refine ⟨rate, amplitude,
    (∑ colour, reference colour * (xiRuleInteriorCount system colour : ℝ)) / (rate - 1),
    rateGreaterThanOne, amplitudePositive,
    div_pos weightedInteriorPositive (sub_pos.mpr rateGreaterThanOne), edgeLimits, ?_⟩
  intro initialColour
  simpa only [mul_comm] using xiVertex_count_normalized_limit system rateGreaterThanOne
    initialColour (colourLimits initialColour)

end
end EIGS

#print axioms EIGS.eigs_vertex_edge_normalized_limits
