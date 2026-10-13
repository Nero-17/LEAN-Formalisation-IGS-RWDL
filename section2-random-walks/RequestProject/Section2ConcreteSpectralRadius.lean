import RequestProject.Section2ConcreteMetric
import RequestProject.Section2PathSpectralRadius

/-! The actual Xi terminal distance scale is the minimum usual complex spectral
radius of genuine rule-path selection matrices. Nonadjacent planting gives a
scale at least two. The explicit simple orientation convention is retained. -/

namespace EIGS

open Filter Topology

variable {K : ℕ}

noncomputable def EIGSData.distanceSpectralRadius (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected) : ℝ :=
  (system.connectedRuleSystem rule_connected).pathMinimumSpectralRadius

theorem EIGSData.rule_paths_use_every_colour (system : EIGSData K)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∀ ruleColour edgeColour : Fin K,
      ∀ path : (system.ruleNetwork ruleColour).toSimpleGraph.Walk
        (system.plantPlus ruleColour) (system.plantMinus ruleColour),
          path.IsPath → (system.ruleNetwork ruleColour).UsesColour path edgeColour := by
  intro ruleColour edgeColour
  exact ((system.ruleNetwork ruleColour).not_reachable_withoutColour_iff_every_path_uses_colour
    ((system.ruleNetwork ruleColour).colourConsistent_of_edgesUnique (rules_unique ruleColour))
    edgeColour _ _).mp (distance_positive ruleColour edgeColour)

theorem EIGSData.two_le_distanceSpectralRadius (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    2 ≤ system.distanceSpectralRadius rule_connected := by
  apply (system.connectedRuleSystem rule_connected).path_spectral_minimum_ge_rule_distance_bound
    (lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt)
    (fun colour => rule_connected colour (system.plantPlus colour) (system.plantMinus colour))
    (system.rule_paths_use_every_colour rules_unique distance_positive) rules_unique
  intro colour
  have distance_gt_one := (rule_connected colour).one_lt_dist_of_ne_of_not_adj
    (system.plant_ne colour) (planting_nonadjacent colour)
  exact_mod_cast (show 2 ≤ (ruleSG system colour).dist
    (system.plantPlus colour) (system.plantMinus colour) from distance_gt_one)

theorem EIGSData.metricLengths_spectral_eigenpair (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lengths : Fin K → ℝ, (∀ colour, 0 < lengths colour) ∧
      0 < system.distanceSpectralRadius rule_connected ∧ (∑ colour, lengths colour) = 1 ∧
      (system.ruleFamily rule_connected).metricLengths lengths =
        system.distanceSpectralRadius rule_connected • lengths := by
  obtain ⟨lengths, _, lengths_positive, rate_positive, normalized, eigenpair, _⟩ :=
    (system.connectedRuleSystem rule_connected).path_spectral_minimum_eigenpair_and_attainment
      (lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt)
      (fun colour => rule_connected colour (system.plantPlus colour) (system.plantMinus colour))
      (system.rule_paths_use_every_colour rules_unique distance_positive)
  refine ⟨lengths, lengths_positive, rate_positive, normalized, ?_⟩
  rw [system.metricLengths_eq_pathRenormMap rule_connected rules_loopless rules_unique
    (fun colour => (lengths_positive colour).le)]
  exact eigenpair

theorem xiSimpleGraph_terminal_distance_spectral_limit (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    1 < system.distanceSpectralRadius rule_connected ∧
      ∃ limit : ℝ, 0 < limit ∧
        Tendsto (fun level =>
          ((XiSimpleGraph system level).dist (xiPositiveTerminal system level)
            (xiNegativeTerminal system level) : ℝ) /
              system.distanceSpectralRadius rule_connected ^ level) atTop (nhds limit) := by
  have rate_gt_one : 1 < system.distanceSpectralRadius rule_connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rule_connected rules_unique planting_nonadjacent
        distance_positive)
  refine ⟨rate_gt_one, ?_⟩
  obtain ⟨limit, vector, _, limit_positive, vector_positive, _, _, convergence⟩ :=
    (system.connectedRuleSystem rule_connected).path_spectral_minimum_normalized_iterate_limit
      (lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt)
      (fun colour => rule_connected colour (system.plantPlus colour) (system.plantMinus colour))
      (system.rule_paths_use_every_colour rules_unique distance_positive)
  refine ⟨limit * vector system.initCol,
    mul_pos limit_positive (vector_positive system.initCol), ?_⟩
  have coordinate_limit := tendsto_pi_nhds.mp convergence system.initCol
  convert coordinate_limit using 1
  ext level
  rw [xiSimpleGraph_terminal_distance_iterate system rule_connected rules_loopless rules_unique]
  rfl

end EIGS

#print axioms EIGS.EIGSData.two_le_distanceSpectralRadius
#print axioms EIGS.EIGSData.metricLengths_spectral_eigenpair
#print axioms EIGS.xiSimpleGraph_terminal_distance_spectral_limit
