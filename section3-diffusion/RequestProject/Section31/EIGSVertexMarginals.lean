import RequestProject.Section31.EIGSVertexMassFromRules
import RequestProject.Section31.EIGSVertexEmpiricalMeasure

/-! The actual uniform vertex ancestor marginals have the independently
constructed edge-address cell probabilities. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal Classical

noncomputable section

variable {K : ℕ} (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))

include ruleConnected plantingNonadjacent distancePositive

theorem xiPrivateVertex_fraction_limit (mass : XiMassParameters system)
    (coarseLevel : ℕ) (cellColour : Fin K) :
    Tendsto (fun offset => (xiInteriorBirthCount system cellColour offset : ℝ) /
      (Fintype.card (XiVtx system (coarseLevel + offset)) : ℝ)) atTop
      (𝓝 (mass.amplitude cellColour / (mass.rate ^ coarseLevel * mass.amplitude system.initCol))) := by
  obtain ⟨rate, amplitude, vertexFactor, rateGreaterThanOne, amplitudePositive,
    factorPositive, edgeLimits, vertexLimits⟩ :=
      eigs_vertex_edge_normalized_limits system ruleConnected plantingNonadjacent distancePositive
  have ratePositive : 0 < rate := zero_lt_one.trans rateGreaterThanOne
  have twoNormalized : Tendsto (fun level : ℕ => (2 : ℝ) / rate ^ level) atTop (𝓝 0) := by
    simpa only [inv_pow, div_eq_mul_inv, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr ratePositive.le)
        ((inv_lt_one₀ ratePositive).mpr rateGreaterThanOne)).const_mul (2 : ℝ)
  have vertexCardinality : ∀ level,
      (Fintype.card (XiVtx {system with initCol := cellColour} level) : ℝ) =
        2 + (xiInteriorBirthCount system cellColour level : ℝ) := by
    intro level
    exact_mod_cast xiVtx_card_eq_two_add_interior_births {system with initCol := cellColour} level
  have birthLimit : Tendsto (fun level => (xiInteriorBirthCount system cellColour level : ℝ) / rate ^ level)
      atTop (𝓝 (vertexFactor * amplitude cellColour)) := by
    convert (vertexLimits cellColour).sub twoNormalized using 1
    · ext level
      rw [vertexCardinality, add_div]
      ring
    · simp only [sub_zero]
  have rootVertexLimit : Tendsto (fun level =>
      (Fintype.card (XiVtx system level) : ℝ) / rate ^ level)
      atTop (𝓝 (vertexFactor * amplitude system.initCol)) := by
    simpa only using vertexLimits system.initCol
  have denominatorLimit : Tendsto (fun offset =>
      (Fintype.card (XiVtx system (coarseLevel + offset)) : ℝ) / rate ^ offset)
      atTop (𝓝 (rate ^ coarseLevel * (vertexFactor * amplitude system.initCol))) := by
    convert (rootVertexLimit.comp (tendsto_add_atTop_nat coarseLevel)).const_mul (rate ^ coarseLevel) using 1
    ext offset
    dsimp only [Function.comp_apply]
    rw [Nat.add_comm offset coarseLevel, pow_add]
    field_simp
  have ratioLimit := birthLimit.div denominatorLimit
    (mul_pos (pow_pos ratePositive coarseLevel) (mul_pos factorPositive (amplitudePositive _))).ne'
  have quotientValue :
      vertexFactor * amplitude cellColour / (rate ^ coarseLevel * (vertexFactor * amplitude system.initCol)) =
        amplitude cellColour / (rate ^ coarseLevel * amplitude system.initCol) := by
    field_simp
  rw [quotientValue] at ratioLimit
  have privateRatioLimit : Tendsto (fun offset =>
      (xiInteriorBirthCount system cellColour offset : ℝ) /
        (Fintype.card (XiVtx system (coarseLevel + offset)) : ℝ)) atTop
      (𝓝 (amplitude cellColour / (rate ^ coarseLevel * amplitude system.initCol))) := by
    convert ratioLimit using 1
    ext offset
    exact (div_div_div_cancel_right₀ (pow_ne_zero offset ratePositive.ne')
      (xiInteriorBirthCount system cellColour offset : ℝ)
      (Fintype.card (XiVtx system (coarseLevel + offset)) : ℝ)).symm
  have weightEquality := tendsto_nhds_unique
    (descendant_fraction_limit_of_normalized_counts system.toRuleData ratePositive amplitudePositive
      edgeLimits coarseLevel cellColour)
    (mass.descendant_fraction_converges coarseLevel cellColour)
  change amplitude cellColour / (rate ^ coarseLevel * amplitude system.initCol) = _ at weightEquality
  rwa [weightEquality] at privateRatioLimit

theorem xiOldVertex_fraction_limit (coarseLevel : ℕ) :
    Tendsto (fun offset => (Fintype.card (XiVtx system coarseLevel) : ℝ) /
      (Fintype.card (XiVtx system (coarseLevel + offset)) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨rate, amplitude, vertexFactor, rateGreaterThanOne, amplitudePositive,
    factorPositive, _, vertexLimits⟩ :=
      eigs_vertex_edge_normalized_limits system ruleConnected plantingNonadjacent distancePositive
  have ratePositive : 0 < rate := zero_lt_one.trans rateGreaterThanOne
  have numeratorLimit : Tendsto (fun offset : ℕ =>
      (Fintype.card (XiVtx system coarseLevel) : ℝ) / rate ^ offset) atTop (𝓝 0) := by
    simpa only [inv_pow, div_eq_mul_inv, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr ratePositive.le)
        ((inv_lt_one₀ ratePositive).mpr rateGreaterThanOne)).const_mul
          (Fintype.card (XiVtx system coarseLevel) : ℝ)
  have rootVertexLimit : Tendsto (fun level =>
      (Fintype.card (XiVtx system level) : ℝ) / rate ^ level)
      atTop (𝓝 (vertexFactor * amplitude system.initCol)) := by
    simpa only using vertexLimits system.initCol
  have denominatorLimit : Tendsto (fun offset =>
      (Fintype.card (XiVtx system (coarseLevel + offset)) : ℝ) / rate ^ offset)
      atTop (𝓝 (rate ^ coarseLevel * (vertexFactor * amplitude system.initCol))) := by
    convert (rootVertexLimit.comp (tendsto_add_atTop_nat coarseLevel)).const_mul (rate ^ coarseLevel) using 1
    ext offset
    dsimp only [Function.comp_apply]
    rw [Nat.add_comm offset coarseLevel, pow_add]
    field_simp
  have quotientLimit := numeratorLimit.div denominatorLimit
    (mul_pos (pow_pos ratePositive coarseLevel) (mul_pos factorPositive (amplitudePositive _))).ne'
  simp only [zero_div] at quotientLimit
  convert quotientLimit using 1
  ext offset
  exact (div_div_div_cancel_right₀ (pow_ne_zero offset ratePositive.ne')
    (Fintype.card (XiVtx system coarseLevel) : ℝ)
    (Fintype.card (XiVtx system (coarseLevel + offset)) : ℝ)).symm

theorem xiVertexCountingMeasure_ancestor_mass_limit (mass : XiMassParameters system)
    (coarseLevel : ℕ) (ancestor : XiEdge system.toRuleData coarseLevel) :
    Tendsto (fun offset => (((xiVertexCountingMeasure system (coarseLevel + offset)).map
      (xiVertexAncestorEdge system coarseLevel offset)) {some ancestor}).toReal)
      atTop (𝓝 (mass.edgeLaw coarseLevel {ancestor}).toReal) := by
  rw [mass.edgeLaw_singleton, ENNReal.toReal_ofReal (mass.edgeWeight_positive coarseLevel ancestor).le]
  simp only [xiVertexCountingMeasure_ancestor_singleton, ENNReal.toReal_div, ENNReal.toReal_natCast,
    XiMassParameters.edgeWeight]
  exact xiPrivateVertex_fraction_limit system ruleConnected plantingNonadjacent distancePositive
    mass coarseLevel (XiCol system.toRuleData coarseLevel ancestor)

theorem xiVertexCountingMeasure_ancestor_none_limit (coarseLevel : ℕ) :
    Tendsto (fun offset => (((xiVertexCountingMeasure system (coarseLevel + offset)).map
      (xiVertexAncestorEdge system coarseLevel offset)) {none}).toReal) atTop (𝓝 0) := by
  simp only [xiVertexCountingMeasure_ancestor_none, ENNReal.toReal_div, ENNReal.toReal_natCast]
  exact xiOldVertex_fraction_limit system ruleConnected plantingNonadjacent distancePositive coarseLevel

end
end EIGS

#print axioms EIGS.xiPrivateVertex_fraction_limit
#print axioms EIGS.xiOldVertex_fraction_limit
#print axioms EIGS.xiVertexCountingMeasure_ancestor_mass_limit
#print axioms EIGS.xiVertexCountingMeasure_ancestor_none_limit

