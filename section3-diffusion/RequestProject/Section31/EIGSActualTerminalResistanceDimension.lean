import RequestProject.Section31.EIGSOriginalDiameterGrowth
import RequestProject.Section2ResistanceSpectralRadius
import RequestProject.Section2ConcreteSimplicity
import RequestProject.Section2SimpleResistance
import RequestProject.Section2LocalScaleLimits
import RequestProject.Section2DegreeGrowth

/-! The actual simple-graph terminal resistance dimension. The paper's
definition uses terminal graph distance; a separate theorem also checks the
same exponent against the actual original unweighted diameter. No abstract
resistance-growth or metric-growth conclusion is assumed. -/

namespace EIGS
open Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

theorem logarithmic_growth_of_positive_normalized_limit {sequence : ℕ → ℝ}
    {rate limit : ℝ} (ratePositive : 0 < rate) (limitPositive : 0 < limit)
    (convergence : Tendsto (fun level => sequence level / rate ^ level) atTop (𝓝 limit)) :
    Tendsto (fun level => Real.log (sequence level) / (level : ℝ)) atTop (𝓝 (Real.log rate)) := by
  have lowerEvent := convergence.eventually (lt_mem_nhds (by linarith : limit / 2 < limit))
  have upperEvent := convergence.eventually (gt_mem_nhds (by linarith : limit < 2 * limit))
  have bounds : ∀ᶠ level in atTop,
      (limit / 2) * rate ^ level ≤ sequence level ∧ sequence level ≤ (2 * limit) * rate ^ level := by
    filter_upwards [lowerEvent, upperEvent] with level lower upper
    have powerPositive := pow_pos ratePositive level
    constructor
    · exact ((lt_div_iff₀ powerPositive).mp lower).le
    · exact ((div_lt_iff₀ powerPositive).mp upper).le
  exact logarithmic_geometric_scale_limit ratePositive (by positivity) (by positivity)
    tendsto_id bounds

theorem xiSimpleGraph_terminal_resistance_canonical_bounds (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ level,
      lower * (system.resistanceSpectralRadius connected distancePositive) ^ level ≤
        effResToBoundary (XiSimpleGraph system level)
          (Finset.univ.erase (xiNegativeTerminal system level)) (xiPositiveTerminal system level) ∧
      effResToBoundary (XiSimpleGraph system level)
          (Finset.univ.erase (xiNegativeTerminal system level)) (xiPositiveTerminal system level) ≤
        upper * (system.resistanceSpectralRadius connected distancePositive) ^ level := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, bounds⟩ :=
    system.resistanceSpectralRadius_iterate_bounds connected distancePositive
  refine ⟨lower, upper, lowerPositive, upperPositive, ?_⟩
  intro level
  have actualEquality := (XiNetwork system level).effRes_eq_simpleGraph_resistance
    (xiNetwork_loopless system connected loopless level)
    (xiNetwork_edges_unique system connected loopless unique plantingNonadjacent level)
    (xiSimpleGraph_connected system connected level)
    (xiPositiveTerminal system level) (xiNegativeTerminal system level) (xiTerminals_distinct system level)
  change _ = effResToBoundary (XiSimpleGraph system level)
    (Finset.univ.erase (xiNegativeTerminal system level)) (xiPositiveTerminal system level) at actualEquality
  rw [← actualEquality, xiNetwork_terminal_effRes system connected (fun _ => 1) (fun _ => zero_le_one)]
  exact bounds level system.initCol

theorem xiSimpleGraph_terminal_resistance_dimension_limit (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    Tendsto (fun level =>
      Real.log (effResToBoundary (XiSimpleGraph system level)
        (Finset.univ.erase (xiNegativeTerminal system level)) (xiPositiveTerminal system level)) /
      Real.log ((XiSimpleGraph system level).dist (xiPositiveTerminal system level)
        (xiNegativeTerminal system level) : ℝ)) atTop
      (𝓝 (Real.log (system.resistanceSpectralRadius connected distancePositive) /
        Real.log (system.distanceSpectralRadius connected))) := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, bounds⟩ :=
    xiSimpleGraph_terminal_resistance_canonical_bounds system connected loopless unique
      plantingNonadjacent distancePositive
  have resistanceLog := logarithmic_geometric_scale_limit
    (system.resistanceSpectralRadius_positive_eigenpair connected distancePositive).1
    lowerPositive upperPositive tendsto_id (Filter.Eventually.of_forall bounds)
  obtain ⟨distanceGreaterThanOne, limit, limitPositive, distanceLimit⟩ :=
    xiSimpleGraph_terminal_distance_spectral_limit system connected loopless unique plantingNonadjacent distancePositive
  have distanceLog := logarithmic_growth_of_positive_normalized_limit
    (zero_lt_one.trans distanceGreaterThanOne) limitPositive distanceLimit
  apply (resistanceLog.div distanceLog (Real.log_pos distanceGreaterThanOne).ne').congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with level positive
  have castNonzero : (level : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  exact div_div_div_cancel_right₀ castNonzero _ _

theorem xiSimpleGraph_terminal_resistanceDimension_eq (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    resistanceDimension
      (fun level => effResToBoundary (XiSimpleGraph system level)
        (Finset.univ.erase (xiNegativeTerminal system level)) (xiPositiveTerminal system level))
      (fun level => ((XiSimpleGraph system level).dist (xiPositiveTerminal system level)
        (xiNegativeTerminal system level) : ℝ)) =
      Real.log (system.resistanceSpectralRadius connected distancePositive) /
        Real.log (system.distanceSpectralRadius connected) :=
  (xiSimpleGraph_terminal_resistance_dimension_limit system connected loopless unique
    plantingNonadjacent distancePositive).limUnder_eq

theorem xiSimpleGraph_terminal_resistance_original_diameter_limit (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    Tendsto (fun level =>
      Real.log (effResToBoundary (XiSimpleGraph system level)
        (Finset.univ.erase (xiNegativeTerminal system level)) (xiPositiveTerminal system level)) /
      Real.log (xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
        (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level)) atTop
      (𝓝 (Real.log (system.resistanceSpectralRadius connected distancePositive) /
        Real.log (system.distanceSpectralRadius connected))) := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, bounds⟩ :=
    xiSimpleGraph_terminal_resistance_canonical_bounds system connected loopless unique
      plantingNonadjacent distancePositive
  have resistanceLog := logarithmic_geometric_scale_limit
    (system.resistanceSpectralRadius_positive_eigenpair connected distancePositive).1
    lowerPositive upperPositive tendsto_id (Filter.Eventually.of_forall bounds)
  obtain ⟨diameterLower, diameterUpper, diameterLowerPositive, diameterUpperPositive, diameterBounds⟩ :=
    xiOriginalDiameter_spectral_growth system connected loopless unique plantingNonadjacent distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  have diameterLog := logarithmic_geometric_scale_limit (zero_lt_one.trans distanceGreaterThanOne)
    diameterLowerPositive diameterUpperPositive tendsto_id diameterBounds
  apply (resistanceLog.div diameterLog (Real.log_pos distanceGreaterThanOne).ne').congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with level positive
  have castNonzero : (level : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  exact div_div_div_cancel_right₀ castNonzero _ _

end
end EIGS

#print axioms EIGS.xiSimpleGraph_terminal_resistance_canonical_bounds
#print axioms EIGS.xiSimpleGraph_terminal_resistance_dimension_limit
#print axioms EIGS.xiSimpleGraph_terminal_resistanceDimension_eq
#print axioms EIGS.xiSimpleGraph_terminal_resistance_original_diameter_limit
