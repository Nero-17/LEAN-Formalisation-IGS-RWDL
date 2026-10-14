import RequestProject.Section31.EIGSPositiveDegreeSpectralData
import RequestProject.Section2DegreeMassGap
import RequestProject.Section2DegreeResistanceGap

/-! Strict spectral comparisons use nonnegativity and a positive eigenvector.
The actual rule graph arguments are retained, without requiring primitivity. -/

namespace EIGS
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

theorem positive_eigenpair_spectralRadius_lt_strict_superinvariant
    {index : Type*} [Fintype index] [DecidableEq index] [Nonempty index]
    (matrix : Matrix index index ℝ) (nonnegative : ∀ row column, 0 ≤ matrix row column)
    (vector : index → ℝ) (vectorPositive : ∀ row, 0 < vector row)
    (eigenpair : matrix.mulVec vector = finiteRealMatrixSpectralRadius matrix • vector)
    (weights : index → ℝ) (weightsPositive : ∀ row, 0 < weights row) (rate : ℝ)
    (strict : ∀ row, matrix.mulVec weights row < rate * weights row) :
    finiteRealMatrixSpectralRadius matrix < rate := by
  obtain ⟨maximumCoordinate, _, maximumRatio⟩ := Finset.univ.exists_max_image
    (fun row => vector row / weights row) Finset.univ_nonempty
  have factorPositive : 0 < vector maximumCoordinate / weights maximumCoordinate :=
    div_pos (vectorPositive _) (weightsPositive _)
  have coordinateBound : ∀ row,
      vector row ≤ (vector maximumCoordinate / weights maximumCoordinate) * weights row := by
    intro row
    exact (div_le_iff₀ (weightsPositive row)).mp (maximumRatio row (Finset.mem_univ _))
  have rowBound : finiteRealMatrixSpectralRadius matrix * vector maximumCoordinate ≤
      (vector maximumCoordinate / weights maximumCoordinate) * matrix.mulVec weights maximumCoordinate := by
    have coordinateEigenpair := congrFun eigenpair maximumCoordinate
    change matrix.mulVec vector maximumCoordinate =
      finiteRealMatrixSpectralRadius matrix * vector maximumCoordinate at coordinateEigenpair
    rw [← coordinateEigenpair]
    calc
      _ ≤ ∑ column, matrix maximumCoordinate column *
          ((vector maximumCoordinate / weights maximumCoordinate) * weights column) :=
        Finset.sum_le_sum (fun column _ =>
          mul_le_mul_of_nonneg_left (coordinateBound column) (nonnegative _ _))
      _ = _ := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro column _
        ring
  have comparison := rowBound.trans_lt (mul_lt_mul_of_pos_left (strict maximumCoordinate) factorPositive)
  have cancellation : (vector maximumCoordinate / weights maximumCoordinate) *
      (rate * weights maximumCoordinate) = rate * vector maximumCoordinate := by
    field_simp [(weightsPositive maximumCoordinate).ne']
  rw [cancellation] at comparison
  nlinarith [vectorPositive maximumCoordinate]

theorem positive_eigenpair_strict_subinvariant_lt_spectralRadius {index : Type*} [Fintype index]
    [DecidableEq index] [Nonempty index] (matrix : Matrix index index ℝ)
    (nonnegative : ∀ row column, 0 ≤ matrix row column)
    (vector : index → ℝ) (vector_positive : ∀ row, 0 < vector row)
    (eigenpair : matrix.mulVec vector = finiteRealMatrixSpectralRadius matrix • vector)
    (weights : index → ℝ)
    (weights_positive : ∀ row, 0 < weights row) (rate : ℝ)
    (strict : ∀ row, rate * weights row < matrix.mulVec weights row) :
    rate < finiteRealMatrixSpectralRadius matrix := by
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
          mul_le_mul_of_nonneg_left (coordinate_bound column) (nonnegative _ _))
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

theorem degree_spectralRadius_lt_mass_of_positive_degree_data {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (degreeData : XiPositiveDegreeSpectralData system) :
    finiteRealMatrixSpectralRadius (degreeMatrix system) < realMatrixSpectralRadius (massMatrixR system.toRuleData) := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  obtain ⟨weights, weightsPositive, _, _, eigenpair⟩ :=
    positive_matrix_spectralRadius_eigenpair
      ((Nat.zero_le system.initCol.val).trans_lt system.initCol.isLt)
      (massMatrixR system.toRuleData) (massMatrixR_positive system rulesConnected distancePositive)
  apply positive_eigenpair_spectralRadius_lt_strict_superinvariant (degreeMatrix system)
    (degreeMatrix_nonneg system) degreeData.vector degreeData.positive degreeData.eigenpair
    (Sum.elim weights weights) (by intro row; cases row <;> exact weightsPositive _) _
  intro row
  rw [degreeMatrix_mulVec_duplicate]
  cases row with
  | inl colour =>
      have coordinate := congrFun eigenpair colour
      change (massMatrixR system.toRuleData).mulVec weights colour =
        realMatrixSpectralRadius (massMatrixR system.toRuleData) * weights colour at coordinate
      change _ < realMatrixSpectralRadius (massMatrixR system.toRuleData) * weights colour
      rw [← coordinate, massMatrixR_mulVec_eq_rule_edge_sum]
      exact rule_terminal_weight_sum_lt_total system rulesConnected rulesLoopless weights weightsPositive colour
        (system.plantPlus colour) (system.plantMinus colour) (system.plant_ne colour) (plantingNonadjacent colour)
  | inr colour =>
      have coordinate := congrFun eigenpair colour
      change (massMatrixR system.toRuleData).mulVec weights colour =
        realMatrixSpectralRadius (massMatrixR system.toRuleData) * weights colour at coordinate
      change _ < realMatrixSpectralRadius (massMatrixR system.toRuleData) * weights colour
      rw [← coordinate, massMatrixR_mulVec_eq_rule_edge_sum]
      exact rule_terminal_weight_sum_lt_total system rulesConnected rulesLoopless weights weightsPositive colour
        (system.plantMinus colour) (system.plantPlus colour) (system.plant_ne colour).symm
        (by intro adjacency; exact plantingNonadjacent colour adjacency.symm)

theorem degree_resistance_spectral_product_gt_one_of_positive_degree_data (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (degreeData : XiPositiveDegreeSpectralData system) :
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
  have gap := positive_eigenpair_strict_subinvariant_lt_spectralRadius (degreeMatrix system)
    (degreeMatrix_nonneg system) degreeData.vector degreeData.positive degreeData.eigenpair
    (Sum.elim (fun colour => (resistances colour)⁻¹) (fun colour => (resistances colour)⁻¹))
    (by intro row; cases row <;> exact inv_pos.mpr (resistances_positive _)) _ strict
  have product_gap := mul_lt_mul_of_pos_right gap rate_positive
  simpa only [inv_mul_cancel₀ rate_positive.ne'] using product_gap

end
end EIGS

#print axioms EIGS.positive_eigenpair_spectralRadius_lt_strict_superinvariant
#print axioms EIGS.positive_eigenpair_strict_subinvariant_lt_spectralRadius
#print axioms EIGS.degree_spectralRadius_lt_mass_of_positive_degree_data
#print axioms EIGS.degree_resistance_spectral_product_gt_one_of_positive_degree_data

