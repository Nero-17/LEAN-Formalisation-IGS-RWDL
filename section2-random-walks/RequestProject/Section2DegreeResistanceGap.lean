import RequestProject.Section2SpectralGrowth
import RequestProject.Section2ResistanceSpectralRadius
import RequestProject.Section31.DirichletThomson

/-! Strict degree/resistance spectral gap from the actual rule Dirichlet
minimum. A boundary spike cannot be harmonic at an interior neighbor. -/

namespace EIGS

open scoped BigOperators Classical
open IGS.Sec31

variable {K : ℕ}

theorem Network.minimum_energy_lt_incident_conductance (network : Network K)
    (resistances : Fin K → ℝ) (resistances_positive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (source sink : network.V) (distinct : source ≠ sink)
    (nonadjacent : ¬ network.toSimpleGraph.Adj source sink)
    (potential : network.V → ℝ)
    (minimal : ∀ competitor : network.V → ℝ, competitor source = 1 → competitor sink = 0 →
      (network.potentialNetwork resistances resistances_positive).energy potential ≤
        (network.potentialNetwork resistances resistances_positive).energy competitor) :
    (network.potentialNetwork resistances resistances_positive).energy potential <
      ∑ edge : network.E,
        ((if network.tail edge = source then (resistances (network.color edge))⁻¹ else 0) +
          (if network.head edge = source then (resistances (network.color edge))⁻¹ else 0)) := by
  let spike : network.V → ℝ := fun vertex => if vertex = source then 1 else 0
  have spike_source : spike source = 1 := by simp [spike]
  have spike_sink : spike sink = 0 := by simp [spike, distinct.symm]
  have energy_le := minimal spike spike_source spike_sink
  have energy_strict :
      (network.potentialNetwork resistances resistances_positive).energy potential <
        (network.potentialNetwork resistances resistances_positive).energy spike := by
    apply lt_of_le_of_ne energy_le
    intro equality
    have spike_minimal : ∀ competitor : network.V → ℝ,
        competitor source = 1 → competitor sink = 0 →
        (network.potentialNetwork resistances resistances_positive).energy spike ≤
          (network.potentialNetwork resistances resistances_positive).energy competitor := by
      intro competitor source_value sink_value
      rw [← equality]
      exact minimal competitor source_value sink_value
    letI : Nontrivial network.V := ⟨⟨source, sink, distinct⟩⟩
    obtain ⟨neighbor, adjacency⟩ := connected.preconnected.exists_adj_of_nontrivial source
    have neighbor_ne_source : neighbor ≠ source := adjacency.ne.symm
    have neighbor_ne_sink : neighbor ≠ sink := by
      intro same
      subst neighbor
      exact nonadjacent adjacency
    have harmonic := (network.potentialNetwork resistances resistances_positive).grad_eq_zero_of_min
      {source, sink} spike spike
      (by
        intro competitor boundary
        apply spike_minimal competitor
        · simpa [spike] using boundary source (by simp)
        · simpa [spike, distinct.symm] using boundary sink (by simp))
      (fun _ _ => rfl) neighbor (by simp [neighbor_ne_source, neighbor_ne_sink])
    have edge_exists : ∃ edge : network.E,
        (network.tail edge = source ∧ network.head edge = neighbor) ∨
          (network.tail edge = neighbor ∧ network.head edge = source) := by
      rcases adjacency.2 with ⟨edge, endpoints⟩ | ⟨edge, endpoints⟩
      · exact ⟨edge, Or.inl endpoints⟩
      · exact ⟨edge, Or.inr endpoints⟩
    obtain ⟨edge, endpoints⟩ := edge_exists
    have negative := (network.potentialNetwork resistances resistances_positive).grad_lt_zero_of_zero_at
      spike neighbor (fun vertex => by simp [spike]; split_ifs <;> norm_num)
      (by simp [spike, neighbor_ne_source]) edge (by
        rcases endpoints with ⟨tail_source, head_neighbor⟩ | ⟨tail_neighbor, head_source⟩
        · exact Or.inr ⟨head_neighbor, by simp [Network.potentialNetwork, tail_source, spike]⟩
        · exact Or.inl ⟨tail_neighbor, by simp [Network.potentialNetwork, head_source, spike]⟩)
    exact (ne_of_lt negative) harmonic
  apply energy_strict.trans_le
  apply Finset.sum_le_sum
  intro edge _
  change (resistances (network.color edge))⁻¹ *
      (spike (network.tail edge) - spike (network.head edge)) ^ 2 ≤ _
  have nonnegative := (inv_pos.mpr (resistances_positive (network.color edge))).le
  by_cases tail_source : network.tail edge = source <;>
    by_cases head_source : network.head edge = source <;>
    simp [spike, tail_source, head_source, nonnegative]

theorem degreeMatrix_mulVec_duplicate (system : EIGSData K) (weights : Fin K → ℝ)
    (row : Fin K ⊕ Fin K) :
    (degreeMatrix system).mulVec (Sum.elim weights weights) row =
      Sum.elim
        (fun colour => ∑ edge : (system.rule colour).E,
          ((if (system.rule colour).tail edge = system.plantPlus colour then weights ((system.rule colour).col edge) else 0) +
           (if (system.rule colour).head edge = system.plantPlus colour then weights ((system.rule colour).col edge) else 0)))
        (fun colour => ∑ edge : (system.rule colour).E,
          ((if (system.rule colour).tail edge = system.plantMinus colour then weights ((system.rule colour).col edge) else 0) +
           (if (system.rule colour).head edge = system.plantMinus colour then weights ((system.rule colour).col edge) else 0))) row := by
  have tail_sum : ∀ colour (vertex : (system.rule colour).V),
      (∑ edgeColour, (ruleTailDeg system colour vertex edgeColour : ℝ) * weights edgeColour) =
        ∑ edge : (system.rule colour).E,
          if (system.rule colour).tail edge = vertex then weights ((system.rule colour).col edge) else 0 := by
    intro colour vertex
    simp only [ruleTailDeg, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro edge _
    by_cases tail_vertex : (system.rule colour).tail edge = vertex <;> simp [tail_vertex]
  have head_sum : ∀ colour (vertex : (system.rule colour).V),
      (∑ edgeColour, (ruleHeadDeg system colour vertex edgeColour : ℝ) * weights edgeColour) =
        ∑ edge : (system.rule colour).E,
          if (system.rule colour).head edge = vertex then weights ((system.rule colour).col edge) else 0 := by
    intro colour vertex
    simp only [ruleHeadDeg, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro edge _
    by_cases head_vertex : (system.rule colour).head edge = vertex <;> simp [head_vertex]
  cases row <;>
    simp only [degreeMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, tail_sum, head_sum, Finset.sum_add_distrib]

theorem primitive_strict_subinvariant_lt_spectralRadius {index : Type*} [Fintype index]
    [DecidableEq index] [Nonempty index] (matrix : Matrix index index ℝ)
    (primitive : matrix.IsPrimitive) (weights : index → ℝ)
    (weights_positive : ∀ row, 0 < weights row) (rate : ℝ)
    (strict : ∀ row, rate * weights row < matrix.mulVec weights row) :
    rate < finiteRealMatrixSpectralRadius matrix := by
  obtain ⟨vector, vector_positive, _, _, eigenpair⟩ :=
    primitive_matrix_spectralRadius_eigenpair_finite matrix primitive
  obtain ⟨maximum_coordinate, _, maximum_ratio⟩ := Finset.univ.exists_max_image
    (fun row => weights row / vector row) (Finset.univ_nonempty)
  have coordinate_bound : ∀ row,
      weights row ≤ (weights maximum_coordinate / vector maximum_coordinate) * vector row := by
    intro row
    exact (div_le_iff₀ (vector_positive row)).mp (maximum_ratio row (Finset.mem_univ _))
  have row_bound : matrix.mulVec weights maximum_coordinate ≤
      finiteRealMatrixSpectralRadius matrix * weights maximum_coordinate := by
    calc
      matrix.mulVec weights maximum_coordinate ≤
          ∑ column, matrix maximum_coordinate column *
            ((weights maximum_coordinate / vector maximum_coordinate) * vector column) :=
        Finset.sum_le_sum (fun column _ =>
          mul_le_mul_of_nonneg_left (coordinate_bound column) (primitive.nonneg _ _))
      _ = (weights maximum_coordinate / vector maximum_coordinate) *
          (finiteRealMatrixSpectralRadius matrix * vector maximum_coordinate) := by
        have coordinate_eigen := congrFun eigenpair maximum_coordinate
        change matrix.mulVec vector maximum_coordinate =
          finiteRealMatrixSpectralRadius matrix * vector maximum_coordinate at coordinate_eigen
        rw [← coordinate_eigen]
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro column _
        ring
      _ = finiteRealMatrixSpectralRadius matrix * weights maximum_coordinate := by
        field_simp [(vector_positive maximum_coordinate).ne']
  have product_strict := (strict maximum_coordinate).trans_le row_bound
  nlinarith [weights_positive maximum_coordinate]

theorem degree_resistance_spectral_product_gt_one (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitive_degree : (degreeMatrix system).IsPrimitive) :
    1 < finiteRealMatrixSpectralRadius (degreeMatrix system) *
      system.resistanceSpectralRadius rule_connected distance_positive := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  obtain ⟨rate_positive, resistances, resistances_positive, eigenpair⟩ :=
    system.resistanceSpectralRadius_positive_eigenpair rule_connected distance_positive
  have plus_strict : ∀ colour,
      (((system.ruleFamily rule_connected).Psi resistances) colour)⁻¹ <
        ∑ edge : (system.rule colour).E,
          ((if (system.rule colour).tail edge = system.plantPlus colour then (resistances ((system.rule colour).col edge))⁻¹ else 0) +
           (if (system.rule colour).head edge = system.plantPlus colour then (resistances ((system.rule colour).col edge))⁻¹ else 0)) := by
    intro colour
    obtain ⟨potential, _, _, minimal, energy⟩ :=
      (system.ruleNetwork colour).exists_minimum_potential_energy_eq_inverse_effRes
        resistances resistances_positive (rule_connected colour) _ _ (system.plant_ne colour)
    have strict := (system.ruleNetwork colour).minimum_energy_lt_incident_conductance
      resistances resistances_positive (rule_connected colour) _ _ (system.plant_ne colour)
      (planting_nonadjacent colour) potential minimal
    rw [energy] at strict
    exact strict
  have minus_strict : ∀ colour,
      (((system.ruleFamily rule_connected).Psi resistances) colour)⁻¹ <
        ∑ edge : (system.rule colour).E,
          ((if (system.rule colour).tail edge = system.plantMinus colour then (resistances ((system.rule colour).col edge))⁻¹ else 0) +
           (if (system.rule colour).head edge = system.plantMinus colour then (resistances ((system.rule colour).col edge))⁻¹ else 0)) := by
    intro colour
    obtain ⟨potential, _, _, minimal, energy⟩ :=
      (system.ruleNetwork colour).exists_minimum_potential_energy_terminal_values
        resistances resistances_positive (rule_connected colour) _ _ (system.plant_ne colour) 0 1
    have strict := (system.ruleNetwork colour).minimum_energy_lt_incident_conductance
      resistances resistances_positive (rule_connected colour) _ _ (system.plant_ne colour).symm
      (fun adjacency => planting_nonadjacent colour adjacency.symm) potential
      (fun competitor source_value sink_value => minimal competitor sink_value source_value)
    rw [energy] at strict
    simpa only [zero_sub, neg_one_sq, one_mul] using strict
  have strict : ∀ row : Fin K ⊕ Fin K,
      (system.resistanceSpectralRadius rule_connected distance_positive)⁻¹ *
          Sum.elim (fun colour => (resistances colour)⁻¹) (fun colour => (resistances colour)⁻¹) row <
        (degreeMatrix system).mulVec
          (Sum.elim (fun colour => (resistances colour)⁻¹) (fun colour => (resistances colour)⁻¹)) row := by
    intro row
    rw [degreeMatrix_mulVec_duplicate]
    cases row with
    | inl colour =>
      have bound := plus_strict colour
      rw [congrFun eigenpair colour] at bound
      simpa only [Sum.elim_inl, Pi.smul_apply, smul_eq_mul, mul_inv_rev, mul_comm] using bound
    | inr colour =>
      have bound := minus_strict colour
      rw [congrFun eigenpair colour] at bound
      simpa only [Sum.elim_inr, Pi.smul_apply, smul_eq_mul, mul_inv_rev, mul_comm] using bound
  have gap := primitive_strict_subinvariant_lt_spectralRadius (degreeMatrix system) primitive_degree
    (Sum.elim (fun colour => (resistances colour)⁻¹) (fun colour => (resistances colour)⁻¹))
    (by intro row; cases row <;> exact inv_pos.mpr (resistances_positive _)) _ strict
  have product_gap := mul_lt_mul_of_pos_right gap rate_positive
  simpa only [inv_mul_cancel₀ rate_positive.ne'] using product_gap

end EIGS

#print axioms EIGS.Network.minimum_energy_lt_incident_conductance
#print axioms EIGS.degreeMatrix_mulVec_duplicate
#print axioms EIGS.primitive_strict_subinvariant_lt_spectralRadius
#print axioms EIGS.degree_resistance_spectral_product_gt_one
