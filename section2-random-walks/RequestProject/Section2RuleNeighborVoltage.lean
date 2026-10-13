import RequestProject.Section2NeighborVoltage
import RequestProject.Section2ResistanceSpectralRadius
import RequestProject.Section31.DirichletThomson
import RequestProject.Section31.EIGSDiscreteTrace

/-! Uniform source-neighbor voltage for the actual rule networks with every
effective resistance vector Psi^[steps](1). No local harmonic estimate is assumed. -/

namespace EIGS

open IGS.Sec31
open scoped BigOperators Classical

variable {K : ℕ}

theorem rule_Psi_source_neighbor_voltage_lower (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower_voltage : ℝ, 0 < lower_voltage ∧
      ∀ colour steps (source sink vertex : (system.ruleNetwork colour).V)
        (potential : (system.ruleNetwork colour).V → ℝ),
        source ≠ sink → vertex ≠ source → vertex ≠ sink →
        potential source = 1 → potential sink = 0 →
        (∀ competitor : (system.ruleNetwork colour).V → ℝ,
          competitor source = 1 → competitor sink = 0 →
          ((system.ruleNetwork colour).potentialNetwork
            ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
            (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) steps)).energy potential ≤
          ((system.ruleNetwork colour).potentialNetwork
            ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
            (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) steps)).energy competitor) →
        ∀ source_edge : (system.ruleNetwork colour).E,
          (((system.ruleNetwork colour).tail source_edge = source ∧
              (system.ruleNetwork colour).head source_edge = vertex) ∨
            ((system.ruleNetwork colour).tail source_edge = vertex ∧
              (system.ruleNetwork colour).head source_edge = source)) →
          lower_voltage ≤ potential vertex := by
  classical
  obtain ⟨resistance_lower, resistance_upper, resistance_lower_positive, resistance_upper_positive, resistance_bounds⟩ :=
    system.resistanceSpectralRadius_iterate_bounds rule_connected distance_positive
  have resistance_rate_positive := (system.resistanceSpectralRadius_positive_eigenpair rule_connected distance_positive).1
  let edge_bound : ℝ := 1 + ∑ colour : Fin K, (Fintype.card (system.ruleNetwork colour).E : ℝ)
  have edge_bound_positive : 0 < edge_bound := by dsimp [edge_bound]; positivity
  have rule_edge_bound : ∀ colour, (Fintype.card (system.ruleNetwork colour).E : ℝ) ≤ edge_bound := by
    intro colour
    have count_sum_bound : (Fintype.card (system.ruleNetwork colour).E : ℝ) ≤
        ∑ other_colour : Fin K, (Fintype.card (system.ruleNetwork other_colour).E : ℝ) :=
      Finset.single_le_sum
        (fun (other_colour : Fin K) _ => Nat.cast_nonneg (Fintype.card (system.ruleNetwork other_colour).E))
        (Finset.mem_univ colour)
    exact count_sum_bound.trans (by dsimp [edge_bound]; linarith)
  let lower_voltage := resistance_lower / (2 * resistance_upper * edge_bound)
  refine ⟨lower_voltage, by positivity,
    fun colour steps source sink vertex potential source_ne_sink vertex_ne_source vertex_ne_sink
      source_value sink_value minimal source_edge source_edge_ends => ?_⟩
  let network := (system.ruleNetwork colour).potentialNetwork
    ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
    (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) steps)
  obtain ⟨poincare_constant, _, poincare_bound⟩ :=
    (system.ruleNetwork colour).exists_potential_poincare_constant
      ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1))
      (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) steps)
      source (rule_connected colour)
  have potential_range : ∀ point, 0 ≤ potential point ∧ potential point ≤ 1 := by
    apply network.range_subset_of_min {source, sink} potential poincare_constant
      (fun values boundary_zero point => poincare_bound values (boundary_zero source (by simp)) point)
    · intro point membership
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using membership :
        point = source ∨ point = sink) with source_eq | sink_eq
      · subst point; simp [source_value]
      · subst point; simp [sink_value]
    · intro _ _; rfl
    · intro competitor boundary
      exact minimal competitor (by simpa [source_value] using boundary source (by simp))
        (by simpa [sink_value] using boundary sink (by simp))
  have harmonic : network.grad potential vertex = 0 := by
    apply network.grad_eq_zero_of_min {source, sink} potential potential
    · intro competitor boundary
      exact minimal competitor (by simpa [source_value] using boundary source (by simp))
        (by simpa [sink_value] using boundary sink (by simp))
    · intro _ _; rfl
    · simpa using And.intro vertex_ne_source vertex_ne_sink
  have source_edge_conductance_lower :
      (resistance_upper * (system.resistanceSpectralRadius rule_connected distance_positive) ^ steps)⁻¹ ≤
        network.cond source_edge := by
    change (resistance_upper * (system.resistanceSpectralRadius rule_connected distance_positive) ^ steps)⁻¹ ≤
      ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1)
        ((system.ruleNetwork colour).color source_edge))⁻¹
    simpa only [one_div] using one_div_le_one_div_of_le
      (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) steps _)
      (resistance_bounds steps _).2
  have conductance_sum_bound : (∑ edge : network.Edge, network.cond edge) ≤
      edge_bound * (resistance_lower *
        (system.resistanceSpectralRadius rule_connected distance_positive) ^ steps)⁻¹ := by
    calc
      _ ≤ ∑ _edge : network.Edge, (resistance_lower *
          (system.resistanceSpectralRadius rule_connected distance_positive) ^ steps)⁻¹ := by
        apply Finset.sum_le_sum
        intro edge _
        change ((system.ruleFamily rule_connected).Psi^[steps] (fun _ => 1)
          ((system.ruleNetwork colour).color edge))⁻¹ ≤ _
        simpa only [one_div] using one_div_le_one_div_of_le (mul_pos resistance_lower_positive (pow_pos resistance_rate_positive steps))
          (resistance_bounds steps _).1
      _ = (Fintype.card (system.ruleNetwork colour).E : ℝ) *
          (resistance_lower * (system.resistanceSpectralRadius rule_connected distance_positive) ^ steps)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rfl
      _ ≤ _ := mul_le_mul_of_nonneg_right (rule_edge_bound colour) (by positivity)
  have conductance_sum_positive : 0 < ∑ edge : network.Edge, network.cond edge :=
    (network.cond_pos source_edge).trans_le (Finset.single_le_sum
      (fun edge _ => (network.cond_pos edge).le) (Finset.mem_univ source_edge))
  have neighbor_bound := network.source_neighbor_voltage_lower potential (fun point => (potential_range point).1)
    source vertex vertex_ne_source.symm source_value harmonic source_edge source_edge_ends
  apply le_trans _ neighbor_bound
  have quotient_bound := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ (resistance_upper *
      (system.resistanceSpectralRadius rule_connected distance_positive) ^ steps)⁻¹)
    (mul_pos (by norm_num : (0 : ℝ) < 2) conductance_sum_positive)
    (mul_le_mul_of_nonneg_left conductance_sum_bound (by norm_num : (0 : ℝ) ≤ 2))
  apply le_trans _ (quotient_bound.trans (div_le_div_of_nonneg_right source_edge_conductance_lower (by positivity)))
  apply le_of_eq
  dsimp [lower_voltage]
  field_simp [ne_of_gt resistance_lower_positive, ne_of_gt resistance_upper_positive,
    ne_of_gt resistance_rate_positive, ne_of_gt edge_bound_positive]
  <;> ring

end EIGS

#print axioms EIGS.rule_Psi_source_neighbor_voltage_lower
