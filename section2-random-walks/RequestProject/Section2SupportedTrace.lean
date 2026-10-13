import RequestProject.Section2GroundedResistanceBounds

/-! Attained actual potential traces supported on the genuine incident star. -/

namespace EIGS

open scoped BigOperators Classical
open IGS.Sec31

variable {K : ℕ}

def Network.substSupport (network : Network K) (rules : RuleFamily K) (inside : network.V → Prop) :
    (network.subst rules).V → Prop
  | Sum.inl vertex => inside vertex
  | Sum.inr private_vertex => inside (network.tail private_vertex.1) ∨ inside (network.head private_vertex.1)

theorem Network.exists_supported_localization (network : Network K) (rules : RuleFamily K)
    (inside : network.V → Prop) (old_values : network.V → ℝ)
    (old_supported : ∀ vertex, ¬ inside vertex → old_values vertex = 0)
    (values : (network.subst rules).V → ℝ)
    (values_old : ∀ vertex, values (Sum.inl vertex) = old_values vertex)
    (resistances : Fin K → ℝ) (resistances_positive : ∀ colour, 0 < resistances colour) :
    ∃ localized : (network.subst rules).V → ℝ,
      (∀ vertex, localized (Sum.inl vertex) = old_values vertex) ∧
      (∀ vertex, ¬ network.substSupport rules inside vertex → localized vertex = 0) ∧
      ((network.subst rules).potentialNetwork resistances resistances_positive).energy localized ≤
        ((network.subst rules).potentialNetwork resistances resistances_positive).energy values := by
  classical
  let localized : (network.subst rules).V → ℝ := fun vertex => match vertex with
    | Sum.inl old_vertex => old_values old_vertex
    | Sum.inr private_vertex => if inside (network.tail private_vertex.1) ∨ inside (network.head private_vertex.1)
        then values (Sum.inr private_vertex) else 0
  have incident_profile : ∀ edge : network.E,
      inside (network.tail edge) ∨ inside (network.head edge) →
      ∀ vertex, localized (network.substEmbed rules edge vertex) = values (network.substEmbed rules edge vertex) := by
    intro edge incident vertex
    by_cases vertex_plus : vertex = rules.βplus (network.color edge)
    · simp only [Network.substEmbed, vertex_plus, ↓reduceDIte, localized, values_old]
    · by_cases vertex_minus : vertex = rules.βminus (network.color edge)
      · simp only [Network.substEmbed, vertex_plus, vertex_minus, (rules.plant_ne _).symm,
          ↓reduceDIte, localized, values_old]
      · simp only [Network.substEmbed, vertex_plus, vertex_minus, ↓reduceDIte, localized, incident, ↓reduceIte]
  have nonincident_profile : ∀ edge : network.E,
      ¬ (inside (network.tail edge) ∨ inside (network.head edge)) →
      ∀ vertex, localized (network.substEmbed rules edge vertex) = 0 := by
    intro edge nonincident vertex
    have tail_zero := old_supported (network.tail edge) (fun membership => nonincident (Or.inl membership))
    have head_zero := old_supported (network.head edge) (fun membership => nonincident (Or.inr membership))
    by_cases vertex_plus : vertex = rules.βplus (network.color edge)
    · simp only [Network.substEmbed, vertex_plus, ↓reduceDIte, localized, tail_zero]
    · by_cases vertex_minus : vertex = rules.βminus (network.color edge)
      · simp only [Network.substEmbed, vertex_plus, vertex_minus, (rules.plant_ne _).symm,
          ↓reduceDIte, localized, head_zero]
      · simp only [Network.substEmbed, vertex_plus, vertex_minus, ↓reduceDIte, localized, nonincident, ↓reduceIte]
  refine ⟨localized, fun _ => rfl, ?_, ?_⟩
  · intro vertex vertex_outside
    cases vertex with
    | inl vertex => exact old_supported vertex vertex_outside
    | inr private_vertex => exact if_neg vertex_outside
  · rw [network.substituted_potential_energy_eq_sum, network.substituted_potential_energy_eq_sum]
    apply Finset.sum_le_sum
    intro edge _
    by_cases incident : inside (network.tail edge) ∨ inside (network.head edge)
    · have profiles_equal := funext (incident_profile edge incident)
      rw [profiles_equal]
    · have profile_zero := funext (nonincident_profile edge incident)
      rw [profile_zero]
      simpa only [FiniteNetwork.energy, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero,
        Finset.sum_const_zero] using
        ((rules.R (network.color edge)).potentialNetwork resistances resistances_positive).energy_nonneg
          (fun vertex => values (network.substEmbed rules edge vertex))

theorem exists_xiPotential_iterated_trace_supported (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (coarse steps : ℕ) (center : XiVtx system coarse)
    (resistances : Fin K → ℝ) (resistances_positive : ∀ colour, 0 < resistances colour) :
    ∃ extension : XiVtx system (coarse + steps) → ℝ,
      (∀ vertex, extension (xiForward system coarse steps vertex) = if vertex = center then 1 else 0) ∧
      (∀ vertex, ¬ xiIncidentStar system coarse center steps vertex → extension vertex = 0) ∧
      ((XiNetwork system (coarse + steps)).potentialNetwork resistances resistances_positive).energy extension =
        ((XiNetwork system coarse).potentialNetwork ((system.ruleFamily rule_connected).Psi^[steps] resistances)
          (ruleFamily_Psi_iterate_positive system rule_connected resistances resistances_positive steps)).energy
            (fun vertex => if vertex = center then 1 else 0) := by
  induction steps generalizing resistances with
  | zero =>
      refine ⟨fun vertex => if vertex = center then 1 else 0, fun _ => rfl, ?_, rfl⟩
      intro vertex vertex_outside
      exact if_neg vertex_outside
  | succ steps induction_hypothesis =>
      obtain ⟨middle, middle_old, middle_supported, middle_energy⟩ := induction_hypothesis
        ((system.ruleFamily rule_connected).Psi resistances)
        (ruleFamily_Psi_positive system rule_connected resistances resistances_positive)
      obtain ⟨extension, extension_old, extension_energy, extension_minimum⟩ :=
        exists_xiPotential_succ_trace system rule_connected resistances resistances_positive (coarse + steps) middle
      obtain ⟨localized, localized_old, localized_supported, localized_le⟩ :=
        (XiNetwork system (coarse + steps)).exists_supported_localization (system.ruleFamily rule_connected)
          (xiIncidentStar system coarse center steps) middle middle_supported extension extension_old
          resistances resistances_positive
      have energies_equal :
          ((XiNetwork system ((coarse + steps) + 1)).potentialNetwork resistances resistances_positive).energy localized =
          ((XiNetwork system ((coarse + steps) + 1)).potentialNetwork resistances resistances_positive).energy extension := by
        refine le_antisymm (by exact localized_le) ?_
        change ((XiNetwork system ((coarse + steps) + 1)).potentialNetwork resistances resistances_positive).energy extension ≤
          ((XiNetwork system ((coarse + steps) + 1)).potentialNetwork resistances resistances_positive).energy localized
        rw [extension_energy]
        exact extension_minimum localized localized_old
      refine ⟨localized, ?_, ?_, ?_⟩
      · intro vertex
        exact (localized_old (xiForward system coarse steps vertex)).trans (middle_old vertex)
      · intro vertex vertex_outside
        cases vertex with
        | inl vertex => exact localized_supported (Sum.inl vertex) vertex_outside
        | inr vertex => exact localized_supported (Sum.inr vertex) vertex_outside
      · exact energies_equal.trans (extension_energy.trans
          (by simpa only [Function.iterate_succ_apply] using middle_energy))

end EIGS

#print axioms EIGS.Network.exists_supported_localization
#print axioms EIGS.exists_xiPotential_iterated_trace_supported
