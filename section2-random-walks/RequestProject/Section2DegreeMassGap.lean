import RequestProject.Section2DegreeResistanceGap
import RequestProject.Section2MassGrowth

/-! A planted terminal misses a positive-weight edge at the other terminal.
Consequently the primitive degree spectral radius is strictly smaller than
the mass spectral radius. Both Perron data and the strict comparison are
derived from actual rules, rather than supplied as dimension hypotheses. -/

namespace EIGS
open scoped BigOperators Classical
noncomputable section

theorem primitive_spectralRadius_lt_strict_superinvariant
    {index : Type*} [Fintype index] [DecidableEq index] [Nonempty index]
    (matrix : Matrix index index ℝ) (primitive : matrix.IsPrimitive)
    (weights : index → ℝ) (weightsPositive : ∀ row, 0 < weights row) (rate : ℝ)
    (strict : ∀ row, matrix.mulVec weights row < rate * weights row) :
    finiteRealMatrixSpectralRadius matrix < rate := by
  obtain ⟨vector, vectorPositive, _, _, eigenpair⟩ :=
    primitive_matrix_spectralRadius_eigenpair_finite matrix primitive
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
          mul_le_mul_of_nonneg_left (coordinateBound column) (primitive.nonneg _ _))
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

theorem Network.incident_weight_sum_lt_total {K : ℕ} (network : Network K)
    (loopless : network.Loopless) (weights : Fin K → ℝ)
    (weightsPositive : ∀ colour, 0 < weights colour) (vertex : network.V)
    (missing : ∃ edge : network.E, network.tail edge ≠ vertex ∧ network.head edge ≠ vertex) :
    (∑ edge : network.E,
      ((if network.tail edge = vertex then weights (network.color edge) else 0) +
       (if network.head edge = vertex then weights (network.color edge) else 0))) <
      ∑ edge : network.E, weights (network.color edge) := by
  apply Finset.sum_lt_sum
  · intro edge _
    by_cases tailEqual : network.tail edge = vertex <;>
      by_cases headEqual : network.head edge = vertex
    · exact False.elim (loopless edge (tailEqual.trans headEqual.symm))
    · simp only [tailEqual, headEqual, ↓reduceIte, add_zero]
      exact le_rfl
    · simp only [tailEqual, headEqual, ↓reduceIte, zero_add]
      exact le_rfl
    · simp only [tailEqual, headEqual, ↓reduceIte, add_zero]
      exact (weightsPositive _).le
  · obtain ⟨edge, tailDifferent, headDifferent⟩ := missing
    refine ⟨edge, Finset.mem_univ _, ?_⟩
    simpa only [tailDifferent, headDifferent, ↓reduceIte, add_zero] using weightsPositive (network.color edge)

theorem rule_terminal_weight_sum_lt_total {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (weights : Fin K → ℝ) (weightsPositive : ∀ colour, 0 < weights colour)
    (colour : Fin K) (terminal otherTerminal : (system.rule colour).V)
    (terminalsDifferent : terminal ≠ otherTerminal)
    (nonadjacent : ¬ (ruleSG system colour).Adj terminal otherTerminal) :
    (∑ edge : (system.rule colour).E,
      ((if (system.rule colour).tail edge = terminal then weights ((system.rule colour).col edge) else 0) +
       (if (system.rule colour).head edge = terminal then weights ((system.rule colour).col edge) else 0))) <
      ∑ edge : (system.rule colour).E, weights ((system.rule colour).col edge) := by
  letI : Nontrivial (system.rule colour).V := ⟨⟨terminal, otherTerminal, terminalsDifferent⟩⟩
  obtain ⟨neighbor, adjacency⟩ :=
    (rulesConnected colour).preconnected.exists_adj_of_nontrivial otherTerminal
  have neighborDifferent : neighbor ≠ terminal := by
    intro equality
    subst neighbor
    exact nonadjacent adjacency.symm
  have missing : ∃ edge : (system.rule colour).E,
      (system.rule colour).tail edge ≠ terminal ∧ (system.rule colour).head edge ≠ terminal := by
    rcases adjacency with ⟨_, forward | reverse⟩
    · obtain ⟨edge, tailEquality, headEquality⟩ := forward
      refine ⟨edge, ?_, ?_⟩
      · rw [tailEquality]
        exact terminalsDifferent.symm
      · rw [headEquality]
        exact neighborDifferent
    · obtain ⟨edge, tailEquality, headEquality⟩ := reverse
      refine ⟨edge, ?_, ?_⟩
      · rw [tailEquality]
        exact neighborDifferent
      · rw [headEquality]
        exact terminalsDifferent.symm
  exact Network.incident_weight_sum_lt_total (system.ruleNetwork colour) (rulesLoopless colour)
    weights weightsPositive terminal missing

theorem massMatrixR_mulVec_eq_rule_edge_sum {K : ℕ} (system : EIGSData K)
    (weights : Fin K → ℝ) (colour : Fin K) :
    (massMatrixR system.toRuleData).mulVec weights colour =
      ∑ edge : (system.rule colour).E, weights ((system.rule colour).col edge) := by
  simp only [massMatrixR, massMatrix, Matrix.mulVec, dotProduct, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro edge _
  simp [EIGSData.toRuleData]

theorem degree_spectralRadius_lt_mass_of_primitive {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    finiteRealMatrixSpectralRadius (degreeMatrix system) < realMatrixSpectralRadius (massMatrixR system.toRuleData) := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  obtain ⟨weights, weightsPositive, _, _, eigenpair⟩ :=
    positive_matrix_spectralRadius_eigenpair
      ((Nat.zero_le system.initCol.val).trans_lt system.initCol.isLt)
      (massMatrixR system.toRuleData) (massMatrixR_positive system rulesConnected distancePositive)
  apply primitive_spectralRadius_lt_strict_superinvariant (degreeMatrix system) primitiveDegree
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

end
end EIGS

#print axioms EIGS.primitive_spectralRadius_lt_strict_superinvariant
#print axioms EIGS.Network.incident_weight_sum_lt_total
#print axioms EIGS.rule_terminal_weight_sum_lt_total
#print axioms EIGS.massMatrixR_mulVec_eq_rule_edge_sum
#print axioms EIGS.degree_spectralRadius_lt_mass_of_primitive
