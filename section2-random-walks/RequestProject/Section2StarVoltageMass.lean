import RequestProject.Section2StarVoltage
import RequestProject.Section2DescendantVoltageMass
import RequestProject.Section2BallLower

/-! Actual positive voltage mass: one genuine child edge is selected in every
coarse source-incident edge, and all its true descendants are counted. -/

namespace EIGS

open scoped BigOperators Classical

variable {K : ℕ}

theorem xiPotentialStep_nonnegative (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (resistances : Fin K → ℝ) (resistances_positive : ∀ colour, 0 < resistances colour)
    (coarse : ℕ) (old_values : XiVtx system coarse → ℝ)
    (old_nonnegative : ∀ vertex, 0 ≤ old_values vertex) :
    ∀ vertex, 0 ≤ xiPotentialStep system rule_connected resistances resistances_positive coarse old_values vertex := by
  intro vertex
  cases vertex with
  | inl old_vertex =>
    rw [xiPotentialStep_old]
    exact old_nonnegative old_vertex
  | inr private_vertex =>
    have endpoint_range := xiPotentialStep_rule_vertex_range system rule_connected resistances resistances_positive
      coarse old_values private_vertex.1 private_vertex.2.val
    have private_embedding :
        embedRuleVtx system coarse private_vertex.1 (XiTail system coarse private_vertex.1)
          (XiHead system coarse private_vertex.1) private_vertex.2.val = Sum.inr private_vertex := by
      simp only [embedRuleVtx, private_vertex.2.property.1, private_vertex.2.property.2, ↓reduceDIte]
    rw [private_embedding] at endpoint_range
    exact (le_min (old_nonnegative _) (old_nonnegative _)).trans endpoint_range.1

theorem xiIncident_nonstationary_voltage_mass_spectral_lower (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rules_unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ mass_lower : ℝ, 0 < mass_lower ∧ ∀ coarse depth (center : XiVtx system coarse),
      mass_lower * (XiSimpleGraph system coarse).degree center *
        realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ depth ≤
      ∑ edge : XiEdge system.toRuleData ((coarse + 1) + depth),
        (xiPotentialValues system rule_connected (coarse + 1) depth (fun _ => 1) (fun _ => by norm_num)
          (xiPotentialStep system rule_connected ((system.ruleFamily rule_connected).Psi^[depth] (fun _ => 1))
            (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) depth)
            coarse (fun vertex => if vertex = center then 1 else 0))
          (XiTail system ((coarse + 1) + depth) edge) +
        xiPotentialValues system rule_connected (coarse + 1) depth (fun _ => 1) (fun _ => by norm_num)
          (xiPotentialStep system rule_connected ((system.ruleFamily rule_connected).Psi^[depth] (fun _ => 1))
            (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) depth)
            coarse (fun vertex => if vertex = center then 1 else 0))
          (XiHead system ((coarse + 1) + depth) edge)) := by
  classical
  obtain ⟨voltage_lower, voltage_lower_positive, child_exists⟩ :=
    xiPotentialStep_positive_incident_child system rule_connected rules_loopless planting_nonadjacent distance_positive
  obtain ⟨edge_mass_lower, edge_mass_lower_positive, edge_mass_bound⟩ :=
    xiReplanted_edge_card_spectral_lower system rule_connected distance_positive
  refine ⟨2 * voltage_lower * edge_mass_lower, by positivity, fun coarse depth center => ?_⟩
  let incident_edges := Finset.univ.filter (fun edge : XiEdge system.toRuleData coarse =>
    XiTail system coarse edge = center ∨ XiHead system coarse edge = center)
  have children_exist : ∀ edge : {edge // edge ∈ incident_edges},
      ∃ child : (system.rule (XiCol system.toRuleData coarse edge.val)).E,
        voltage_lower ≤ xiPotentialStep system rule_connected
          ((system.ruleFamily rule_connected).Psi^[depth] (fun _ => 1))
          (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) depth)
          coarse (fun vertex => if vertex = center then 1 else 0)
          (XiTail system (coarse + 1) ⟨edge.val, child⟩) ∧
        voltage_lower ≤ xiPotentialStep system rule_connected
          ((system.ruleFamily rule_connected).Psi^[depth] (fun _ => 1))
          (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) depth)
          coarse (fun vertex => if vertex = center then 1 else 0)
          (XiHead system (coarse + 1) ⟨edge.val, child⟩) := fun edge =>
    child_exists coarse depth center edge.val (Finset.mem_filter.mp edge.property).2
  choose children children_positive using children_exist
  let selected_child : {edge // edge ∈ incident_edges} → XiEdge system.toRuleData (coarse + 1) :=
    fun edge => ⟨edge.val, children edge⟩
  have child_injective : Function.Injective selected_child := by
    intro first second same
    exact Subtype.ext (congrArg Sigma.fst same)
  let selected := Finset.univ.image selected_child
  have selected_card : selected.card = incident_edges.card := by
    simp only [selected, Finset.card_image_of_injective _ child_injective,
      Finset.card_univ, Fintype.card_coe]
  have incident_card_degree : (incident_edges.card : ℝ) = (XiSimpleGraph system coarse).degree center := by
    dsimp [incident_edges]
    rw [Finset.card_filter, Nat.cast_sum]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact (XiNetwork system coarse).incident_edge_count_eq_degree
      (xiNetwork_loopless system rule_connected rules_loopless coarse)
      (xiNetwork_edges_unique system rule_connected rules_loopless rules_unique planting_nonadjacent coarse) center
  have selected_positive : ∀ edge ∈ selected,
      voltage_lower ≤ xiPotentialStep system rule_connected
        ((system.ruleFamily rule_connected).Psi^[depth] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) depth)
        coarse (fun vertex => if vertex = center then 1 else 0) (XiTail system (coarse + 1) edge) ∧
      voltage_lower ≤ xiPotentialStep system rule_connected
        ((system.ruleFamily rule_connected).Psi^[depth] (fun _ => 1))
        (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) depth)
        coarse (fun vertex => if vertex = center then 1 else 0) (XiHead system (coarse + 1) edge) := by
    intro edge membership
    obtain ⟨original, _, rfl⟩ := Finset.mem_image.mp membership
    exact children_positive original
  have descendant_mass := xiPotentialValues_descendant_voltage_mass_lower system rule_connected (coarse + 1) depth
    (xiPotentialStep system rule_connected ((system.ruleFamily rule_connected).Psi^[depth] (fun _ => 1))
      (ruleFamily_Psi_iterate_positive system rule_connected (fun _ => 1) (fun _ => by norm_num) depth)
      coarse (fun vertex => if vertex = center then 1 else 0))
    (xiPotentialStep_nonnegative system rule_connected _ _ coarse _ (fun vertex => by split <;> norm_num))
    (fun _ => 1) (fun _ => by norm_num) selected voltage_lower selected_positive
  apply le_trans _ descendant_mass
  calc
    _ = ∑ _edge ∈ selected, 2 * voltage_lower *
        (edge_mass_lower * realMatrixSpectralRadius (massMatrixR system.toRuleData) ^ depth) := by
      rw [Finset.sum_const, nsmul_eq_mul, selected_card, incident_card_degree]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun edge _ =>
      mul_le_mul_of_nonneg_left (edge_mass_bound _ depth) (by positivity))

end EIGS

#print axioms EIGS.xiPotentialStep_nonnegative
#print axioms EIGS.xiIncident_nonstationary_voltage_mass_spectral_lower
