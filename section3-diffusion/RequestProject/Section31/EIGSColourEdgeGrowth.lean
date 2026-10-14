import RequestProject.Section31.EIGSAnalyticTimeScale
import RequestProject.Section31.FiniteMarkovVectorRange

/-! Uniform actual colour edge-count bounds after the first substitution.
Strict positivity of the mass matrix supplies each colour from every old
edge. Total edge growth alone then supplies both bounds. Candidate source. -/

namespace EIGS
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

theorem colour_edge_geometric_growth (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ level colour,
      lower * mass.rate ^ (level + 1) ≤ (chiCount system.toRuleData (level + 1) colour : ℝ) ∧
      (chiCount system.toRuleData (level + 1) colour : ℝ) ≤ upper * mass.rate ^ (level + 1) := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  let entries : Fin K × Fin K → ℝ := fun pair => massMatrixR system.toRuleData pair.1 pair.2
  have matrixPositive := massMatrixR_positive system connected distancePositive
  have minimumPositive : 0 < finiteVectorMinimum entries :=
    (Finset.lt_inf'_iff _).2 (fun pair _ => matrixPositive pair.1 pair.2)
  obtain ⟨lower, upper, lowerPositive, upperPositive, totalGrowth⟩ :=
    mass_geometric_growth system mass.amplitude_positive mass.eigenpair mass.rate_positive
  refine ⟨lower * finiteVectorMinimum entries / mass.rate, upper,
    div_pos (mul_pos lowerPositive minimumPositive) mass.rate_positive, upperPositive, ?_⟩
  intro level colour
  have componentLower : finiteVectorMinimum entries * (totalEdges system.toRuleData level : ℝ) ≤
      (chiCount system.toRuleData (level + 1) colour : ℝ) := by
    change _ ≤ chiVec system.toRuleData (level + 1) colour
    rw [totalEdges_eq_sum, chiVec_succ]
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro oldColour _
    have nonnegative : 0 ≤ chiVec system.toRuleData level oldColour := Nat.cast_nonneg _
    have entryLower := (finiteVector_range_bounds entries (oldColour, colour)).1
    simpa only [entries, mul_comm] using mul_le_mul_of_nonneg_left entryLower nonnegative
  have componentUpper : (chiCount system.toRuleData (level + 1) colour : ℝ) ≤
      (totalEdges system.toRuleData (level + 1) : ℝ) := by
    rw [totalEdges_eq_sum]
    exact Finset.single_le_sum (fun oldColour _ => (Nat.cast_nonneg _ :
      0 ≤ chiVec system.toRuleData (level + 1) oldColour)) (Finset.mem_univ colour)
  constructor
  · calc
      lower * finiteVectorMinimum entries / mass.rate * mass.rate ^ (level + 1) =
          finiteVectorMinimum entries * (lower * mass.rate ^ level) := by
        rw [pow_succ]
        field_simp [mass.rate_positive.ne'] <;> ring
      _ ≤ finiteVectorMinimum entries * (totalEdges system.toRuleData level : ℝ) :=
        mul_le_mul_of_nonneg_left (totalGrowth level).1 minimumPositive.le
      _ ≤ (chiCount system.toRuleData (level + 1) colour : ℝ) := componentLower
  · exact componentUpper.trans (totalGrowth (level + 1)).2

theorem colour_edge_geometric_growth_from_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ level colour,
      lower * (realMatrixSpectralRadius (massMatrixR system.toRuleData)) ^ (level + 1) ≤
        (chiCount system.toRuleData (level + 1) colour : ℝ) ∧
      (chiCount system.toRuleData (level + 1) colour : ℝ) ≤
        upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData)) ^ (level + 1) := by
  let mass := xiMassParametersOfRules system connected distancePositive
  have actual := colour_edge_geometric_growth system connected distancePositive mass
  simpa only [XiMassParameters.rate_eq_spectralRadius system mass] using actual

end
end EIGS

#print axioms EIGS.colour_edge_geometric_growth
#print axioms EIGS.colour_edge_geometric_growth_from_rules
