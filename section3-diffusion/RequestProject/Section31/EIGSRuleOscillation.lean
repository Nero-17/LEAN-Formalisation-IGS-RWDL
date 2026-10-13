import RequestProject.Section2Concrete
import RequestProject.Section31.DirichletThomson

/-!
# A strict oscillation factor for the actual harmonic rule profiles

The profiles, their Poincaré constants and their strict edge bounds are all
derived from the original graphs. Distance positivity excludes shortcut edges
for multiple colours; the one-colour distance clause covers the remaining case.
-/

namespace EIGS

open IGS.Sec31

variable {K : ℕ}

theorem rule_terminals_nonadjacent_standing (system : EIGSData K)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (colour : Fin K) :
    ¬ (ruleSG system colour).Adj (system.plantPlus colour) (system.plantMinus colour) := by
  by_cases oneColour : K = 1
  · intro adjacent
    have distanceOne := SimpleGraph.dist_eq_one_iff_adj.2 adjacent
    have distanceLower := oneColourDistance oneColour colour
    omega
  · have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
    exact (system.ruleNetwork colour).terminals_nonadjacent_of_distance_positive
      (system.plantPlus colour) (system.plantMinus colour) (by omega) (distancePositive colour)

private theorem exists_uniform_strict_bound {Index : Type*} [Fintype Index]
    (values : Index → ℝ) (valuesStrict : ∀ index, values index < 1) :
    ∃ bound : ℝ, 0 < bound ∧ bound < 1 ∧ ∀ index, values index ≤ bound := by
  classical
  have finiteBound : ∀ selected : Finset Index,
      ∃ bound : ℝ, 0 < bound ∧ bound < 1 ∧ ∀ index ∈ selected, values index ≤ bound := by
    intro selected
    induction selected using Finset.induction_on with
    | empty => exact ⟨1 / 2, by norm_num, by norm_num, by simp⟩
    | @insert index selected notSelected induction =>
        obtain ⟨bound, boundPositive, boundStrict, selectedBound⟩ := induction
        refine ⟨max bound ((values index + 1) / 2),
          boundPositive.trans_le (le_max_left _ _), max_lt boundStrict (by linarith [valuesStrict index]), ?_⟩
        intro other membership
        rcases Finset.mem_insert.1 membership with equality | membership
        · subst other
          exact (by linarith [valuesStrict index] : values index ≤ (values index + 1) / 2).trans
            (le_max_right _ _)
        · exact (selectedBound other membership).trans (le_max_left _ _)
  obtain ⟨bound, boundPositive, boundStrict, allBound⟩ := finiteBound Finset.univ
  exact ⟨bound, boundPositive, boundStrict, fun index => allBound index (Finset.mem_univ index)⟩

/-- Actual two-terminal harmonic profiles have one common strictly contracting
edge factor. No Poincaré bound, profile or oscillation estimate is assumed. -/
theorem exists_rule_harmonic_profiles_strict_oscillation (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour) :
    ∃ profiles : ∀ colour, (system.rule colour).V → ℝ,
      ∃ contractionFactor : ℝ, 0 < contractionFactor ∧ contractionFactor < 1 ∧
        (∀ colour, profiles colour (system.plantPlus colour) = 1) ∧
        (∀ colour, profiles colour (system.plantMinus colour) = 0) ∧
        (∀ colour (competitor : (system.rule colour).V → ℝ),
          competitor (system.plantPlus colour) = 1 → competitor (system.plantMinus colour) = 0 →
          ((system.ruleNetwork colour).potentialNetwork resistances resistancesPositive).energy (profiles colour) ≤
            ((system.ruleNetwork colour).potentialNetwork resistances resistancesPositive).energy competitor) ∧
        (∀ colour (edge : (system.rule colour).E),
          |profiles colour ((system.rule colour).tail edge) -
            profiles colour ((system.rule colour).head edge)| ≤ contractionFactor) := by
  classical
  have profilesExist : ∀ colour, ∃ profile : (system.rule colour).V → ℝ,
      profile (system.plantPlus colour) = 1 ∧ profile (system.plantMinus colour) = 0 ∧
      (∀ competitor : (system.rule colour).V → ℝ,
        competitor (system.plantPlus colour) = 1 → competitor (system.plantMinus colour) = 0 →
        ((system.ruleNetwork colour).potentialNetwork resistances resistancesPositive).energy profile ≤
          ((system.ruleNetwork colour).potentialNetwork resistances resistancesPositive).energy competitor) ∧
      (∀ edge : (system.rule colour).E,
        |profile ((system.rule colour).tail edge) - profile ((system.rule colour).head edge)| < 1) := by
    intro colour
    obtain ⟨profile, profilePlus, profileMinus, profileMinimal, profileEnergy⟩ :=
      (system.ruleNetwork colour).exists_minimum_potential_energy_eq_inverse_effRes resistances
        resistancesPositive (rulesConnected colour) (system.plantPlus colour) (system.plantMinus colour)
          (system.plant_ne colour)
    obtain ⟨poincareConstant, poincareNonnegative, poincareBound⟩ :=
      (system.ruleNetwork colour).exists_potential_poincare_constant resistances resistancesPositive
        (system.plantPlus colour) (rulesConnected colour)
    have profileBoundaryMinimal : ∀ competitor : (system.rule colour).V → ℝ,
        (∀ vertex ∈ ({system.plantMinus colour, system.plantPlus colour} : Finset (system.rule colour).V),
          competitor vertex = profile vertex) →
        ((system.ruleNetwork colour).potentialNetwork resistances resistancesPositive).energy profile ≤
          ((system.ruleNetwork colour).potentialNetwork resistances resistancesPositive).energy competitor := by
      intro competitor competitorBoundary
      apply profileMinimal competitor
      · simpa [profilePlus] using competitorBoundary (system.plantPlus colour) (by simp)
      · simpa [profileMinus] using competitorBoundary (system.plantMinus colour) (by simp)
    have noShortcut : ∀ edge : (system.rule colour).E,
        ¬ (((system.rule colour).tail edge = system.plantMinus colour ∧
              (system.rule colour).head edge = system.plantPlus colour) ∨
            ((system.rule colour).tail edge = system.plantPlus colour ∧
              (system.rule colour).head edge = system.plantMinus colour)) := by
      intro edge shortcut
      apply rule_terminals_nonadjacent_standing system distancePositive oneColourDistance colour
      refine ⟨system.plant_ne colour, ?_⟩
      rcases shortcut with shortcut | shortcut
      · exact Or.inr ⟨edge, shortcut.1, shortcut.2⟩
      · exact Or.inl ⟨edge, shortcut.1, shortcut.2⟩
    refine ⟨profile, profilePlus, profileMinus, profileMinimal, ?_⟩
    exact ((system.ruleNetwork colour).potentialNetwork resistances resistancesPositive).edge_osc_lt_one_of_no_shortcut
      (system.plantMinus colour) (system.plantPlus colour) poincareConstant profile
      (fun values boundaryZero vertex => poincareBound values
        (boundaryZero (system.plantPlus colour) (by simp)) vertex)
      profileMinus profilePlus profile (fun _ _ => rfl) profileBoundaryMinimal noShortcut
  choose profiles profilesPlus profilesMinus profilesMinimal profilesOscillation using profilesExist
  obtain ⟨contractionFactor, factorPositive, factorStrict, edgeBound⟩ :=
    exists_uniform_strict_bound
      (fun indexedEdge : Σ colour, (system.rule colour).E =>
        |profiles indexedEdge.1 ((system.rule indexedEdge.1).tail indexedEdge.2) -
          profiles indexedEdge.1 ((system.rule indexedEdge.1).head indexedEdge.2)|)
      (fun indexedEdge => profilesOscillation indexedEdge.1 indexedEdge.2)
  exact ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
    profilesMinimal, fun colour edge => edgeBound ⟨colour, edge⟩⟩

end EIGS
