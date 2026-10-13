import RequestProject.Section2MassResistanceDistance
import RequestProject.Section2SpectralGrowth
import RequestProject.Section2ResistanceSpectralRadius
import RequestProject.Section2MultiStepSpectralBall

/-! The mass--resistance spectral product dominates the square of the actual
distance spectral radius. All comparison sequences are those of the original
substitution networks, and all Perron parameters are constructed from rules. -/

namespace EIGS

open Filter Topology
open scoped BigOperators

private theorem geometric_base_le_of_comparison
    {first second lower upper : ℝ} (firstPositive : 0 < first)
    (secondNonnegative : 0 ≤ second) (lowerPositive : 0 < lower)
    (bounds : ∀ level : ℕ, lower * first ^ level ≤ upper * second ^ level) :
    first ≤ second := by
  by_contra notLe
  have ratioNonnegative : 0 ≤ second / first := div_nonneg secondNonnegative firstPositive.le
  have ratioLessThanOne : second / first < 1 := (div_lt_one firstPositive).mpr (lt_of_not_ge notLe)
  have convergence := (tendsto_pow_atTop_nhds_zero_of_lt_one ratioNonnegative ratioLessThanOne).const_mul upper
  have allLower : ∀ level : ℕ, lower ≤ upper * (second / first) ^ level := by
    intro level
    rw [div_pow, ← mul_div_assoc]
    exact (le_div_iff₀ (pow_pos firstPositive level)).mpr (bounds level)
  have contradiction := ge_of_tendsto convergence (Filter.Eventually.of_forall allLower)
  have : lower ≤ 0 := by simpa using contradiction
  exact (not_le_of_gt lowerPositive) this

variable {K : ℕ}

theorem EIGSData.distanceSpectralRadius_sq_le_mass_mul_resistance
    (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    system.distanceSpectralRadius connected ^ 2 ≤
      realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius connected distancePositive := by
  obtain ⟨lengths, lengthsPositive, ratePositive, normalized, eigenpair⟩ :=
    system.metricLengths_spectral_eigenpair connected loopless unique distancePositive
  obtain ⟨massPositive, massLower, massUpper, massLowerPositive, massUpperPositive, massBounds⟩ :=
    eigs_mass_spectral_growth system connected distancePositive
  have resistancePositive :=
    (system.resistanceSpectralRadius_positive_eigenpair connected distancePositive).1
  obtain ⟨resistanceLower, resistanceUpper, resistanceLowerPositive, resistanceUpperPositive, resistanceBounds⟩ :=
    system.resistanceSpectralRadius_iterate_bounds connected distancePositive
  have lengthsAtMostOne : lengths ≤ fun _ => (1 : ℝ) := by
    intro colour
    rw [← normalized]
    exact Finset.single_le_sum (fun other _ => (lengthsPositive other).le) (Finset.mem_univ colour)
  apply geometric_base_le_of_comparison (upper := massUpper * resistanceUpper) (sq_pos_of_pos ratePositive)
    (mul_pos massPositive resistancePositive).le (sq_pos_of_pos (lengthsPositive system.initCol))
  intro level
  have unitDistanceLower := (XiNetwork system level).weightedDistance_mono
    (xiSimpleGraph_connected system connected level) (fun colour => (lengthsPositive colour).le)
    lengthsAtMostOne (xiPositiveTerminal system level) (xiNegativeTerminal system level)
  rw [xiNetwork_terminal_metric_iterate system connected (fun colour => (lengthsPositive colour).le),
    system.metricLengths_iterate_eigenpair connected ratePositive.le eigenpair] at unitDistanceLower
  simp only [Pi.smul_apply, smul_eq_mul] at unitDistanceLower
  have finiteBound := (XiNetwork system level).distance_sq_le_edge_card_mul_effRes
    (xiSimpleGraph_connected system connected level) (xiPositiveTerminal system level)
    (xiNegativeTerminal system level) (xiTerminals_distinct system level)
    (xiNetwork_terminal_flow system connected level)
  rw [xiNetwork_terminal_effRes system connected (fun _ => 1) (fun _ => zero_le_one)] at finiteBound
  change (XiNetwork system level).weightedDistance (fun _ => 1)
      (xiPositiveTerminal system level) (xiNegativeTerminal system level) ^ 2 ≤
    (totalEdges system.toRuleData level : ℝ) *
      (system.ruleFamily connected).Psi^[level] (fun _ => 1) system.initCol at finiteBound
  have resistanceNonnegative : 0 ≤ (system.ruleFamily connected).Psi^[level] (fun _ => 1) system.initCol :=
    (mul_pos resistanceLowerPositive (pow_pos resistancePositive level)).le.trans (resistanceBounds level system.initCol).1
  have upperProduct := mul_le_mul (massBounds level).2 (resistanceBounds level system.initCol).2
    resistanceNonnegative (mul_pos massUpperPositive (pow_pos massPositive level)).le
  have squaredLower :
      (system.distanceSpectralRadius connected ^ level * lengths system.initCol) ^ 2 ≤
        (XiNetwork system level).weightedDistance (fun _ => 1)
          (xiPositiveTerminal system level) (xiNegativeTerminal system level) ^ 2 := by
    exact sq_le_sq₀ (mul_pos (pow_pos ratePositive level) (lengthsPositive system.initCol)).le
      ((XiNetwork system level).weightedDistance_nonnegative
        (xiSimpleGraph_connected system connected level) (fun _ => zero_le_one) _ _) |>.mpr unitDistanceLower
  have inequality := squaredLower.trans (finiteBound.trans upperProduct)
  convert inequality using 1 <;> simp only [mul_pow, pow_right_comm] <;> ring

end EIGS

#print axioms EIGS.EIGSData.distanceSpectralRadius_sq_le_mass_mul_resistance
