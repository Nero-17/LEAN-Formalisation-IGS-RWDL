import RequestProject.Section31.DirichletThomson

/-!
# The potential trace of actual graph substitution

Each edge is replaced by its private rule copy with the two terminals glued to
the old endpoints. The minimum is obtained by gluing the finite-network
minimizers proved in `DirichletThomson`; no trace identity is assumed.
-/

namespace EIGS.Network

open IGS.Sec31

variable {K : ℕ} (network : Network K) (rules : RuleFamily K)

theorem substituted_potential_energy_eq_sum
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (potential : (network.subst rules).V → ℝ) :
    ((network.subst rules).potentialNetwork resistances resistancesPositive).energy potential =
      ∑ edge : network.E,
        ((rules.R (network.color edge)).potentialNetwork resistances resistancesPositive).energy
          (fun vertex => potential (network.substEmbed rules edge vertex)) := by
  simp only [FiniteNetwork.energy, potentialNetwork, subst]
  rw [Fintype.sum_sigma]

/-- The value of the actual substituted Dirichlet minimum, with arbitrary old
vertex values and positive resistances on the unchanged rule edges. -/
theorem exists_substituted_potential_trace
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (rulesConnected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    (oldValues : network.V → ℝ) :
    ∃ extension : (network.subst rules).V → ℝ,
      (∀ vertex, extension (Sum.inl vertex) = oldValues vertex) ∧
      ((network.subst rules).potentialNetwork resistances resistancesPositive).energy extension =
        ∑ edge : network.E,
          (oldValues (network.tail edge) - oldValues (network.head edge)) ^ 2 *
            (rules.Psi resistances (network.color edge))⁻¹ ∧
      (∀ competitor : (network.subst rules).V → ℝ,
        (∀ vertex, competitor (Sum.inl vertex) = oldValues vertex) →
        (∑ edge : network.E,
          (oldValues (network.tail edge) - oldValues (network.head edge)) ^ 2 *
            (rules.Psi resistances (network.color edge))⁻¹) ≤
          ((network.subst rules).potentialNetwork resistances resistancesPositive).energy competitor) := by
  classical
  have cellMinima : ∀ edge : network.E,
      ∃ profile : (rules.R (network.color edge)).V → ℝ,
        profile (rules.βplus (network.color edge)) = oldValues (network.tail edge) ∧
        profile (rules.βminus (network.color edge)) = oldValues (network.head edge) ∧
        (∀ competitor : (rules.R (network.color edge)).V → ℝ,
          competitor (rules.βplus (network.color edge)) = oldValues (network.tail edge) →
          competitor (rules.βminus (network.color edge)) = oldValues (network.head edge) →
          ((rules.R (network.color edge)).potentialNetwork resistances resistancesPositive).energy profile ≤
            ((rules.R (network.color edge)).potentialNetwork resistances resistancesPositive).energy competitor) ∧
        ((rules.R (network.color edge)).potentialNetwork resistances resistancesPositive).energy profile =
          (oldValues (network.tail edge) - oldValues (network.head edge)) ^ 2 *
            (rules.Psi resistances (network.color edge))⁻¹ := by
    intro edge
    exact (rules.R (network.color edge)).exists_minimum_potential_energy_terminal_values
      resistances resistancesPositive (rulesConnected (network.color edge))
      (rules.βplus (network.color edge)) (rules.βminus (network.color edge))
      (rules.plant_ne (network.color edge)) (oldValues (network.tail edge))
      (oldValues (network.head edge))
  choose profiles profilesSource profilesSink profilesMinimal profilesEnergy using cellMinima
  let extension : (network.subst rules).V → ℝ := fun vertex =>
    match vertex with
    | Sum.inl oldVertex => oldValues oldVertex
    | Sum.inr privateVertex => profiles privateVertex.1 privateVertex.2.val
  have extensionRestriction : ∀ edge (vertex : (rules.R (network.color edge)).V),
      extension (network.substEmbed rules edge vertex) = profiles edge vertex := by
    intro edge vertex
    by_cases vertexSource : vertex = rules.βplus (network.color edge)
    · subst vertex
      simp [extension, substEmbed, profilesSource]
    · by_cases vertexSink : vertex = rules.βminus (network.color edge)
      · subst vertex
        simp [extension, substEmbed, vertexSource, profilesSink]
      · simp [extension, substEmbed, vertexSource, vertexSink]
  refine ⟨extension, fun vertex => rfl, ?_, ?_⟩
  · rw [network.substituted_potential_energy_eq_sum]
    apply Finset.sum_congr rfl
    intro edge _
    have restrictionEquality : (fun vertex => extension (network.substEmbed rules edge vertex)) =
        profiles edge := funext (extensionRestriction edge)
    rw [restrictionEquality]
    exact profilesEnergy edge
  · intro competitor competitorOldValues
    rw [network.substituted_potential_energy_eq_sum]
    apply Finset.sum_le_sum
    intro edge _
    rw [← profilesEnergy edge]
    apply profilesMinimal edge
    · simpa [substEmbed] using competitorOldValues (network.tail edge)
    · simpa [substEmbed, (rules.plant_ne (network.color edge)).symm] using
        competitorOldValues (network.head edge)

/-- The gluing construction attains the global minimum against every competitor
with the prescribed skeleton values. -/
theorem exists_substituted_potential_minimum
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (rulesConnected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    (oldValues : network.V → ℝ) :
    ∃ extension : (network.subst rules).V → ℝ,
      (∀ vertex, extension (Sum.inl vertex) = oldValues vertex) ∧
      (∀ competitor : (network.subst rules).V → ℝ,
        (∀ vertex, competitor (Sum.inl vertex) = oldValues vertex) →
        ((network.subst rules).potentialNetwork resistances resistancesPositive).energy extension ≤
          ((network.subst rules).potentialNetwork resistances resistancesPositive).energy competitor) ∧
      ((network.subst rules).potentialNetwork resistances resistancesPositive).energy extension =
        ∑ edge : network.E,
          (oldValues (network.tail edge) - oldValues (network.head edge)) ^ 2 *
            (rules.Psi resistances (network.color edge))⁻¹ := by
  obtain ⟨extension, extensionOld, extensionEnergy, lowerBound⟩ :=
    network.exists_substituted_potential_trace rules resistances resistancesPositive rulesConnected oldValues
  refine ⟨extension, extensionOld, ?_, extensionEnergy⟩
  intro competitor competitorOld
  rw [extensionEnergy]
  exact lowerBound competitor competitorOld

/-- A positive renormalization eigenvector makes the actual substituted trace
equal to the coarse potential energy after the Perron scaling. The eigenpair is
an input to this intermediate algebraic specialization, not a trace premise. -/
theorem exists_substituted_eigenvector_trace
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (rulesConnected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (renormalizationEigenpair : ∀ colour,
      rules.Psi resistances colour = resistanceRate * resistances colour)
    (oldValues : network.V → ℝ) :
    ∃ extension : (network.subst rules).V → ℝ,
      (∀ vertex, extension (Sum.inl vertex) = oldValues vertex) ∧
      resistanceRate *
          ((network.subst rules).potentialNetwork resistances resistancesPositive).energy extension =
        (network.potentialNetwork resistances resistancesPositive).energy oldValues ∧
      (∀ competitor : (network.subst rules).V → ℝ,
        (∀ vertex, competitor (Sum.inl vertex) = oldValues vertex) →
        (network.potentialNetwork resistances resistancesPositive).energy oldValues ≤
          resistanceRate *
            ((network.subst rules).potentialNetwork resistances resistancesPositive).energy competitor) := by
  obtain ⟨extension, extensionOld, extensionEnergy, lowerBound⟩ :=
    network.exists_substituted_potential_trace rules resistances resistancesPositive rulesConnected oldValues
  have scaledTrace : resistanceRate *
      (∑ edge : network.E,
        (oldValues (network.tail edge) - oldValues (network.head edge)) ^ 2 *
          (rules.Psi resistances (network.color edge))⁻¹) =
      (network.potentialNetwork resistances resistancesPositive).energy oldValues := by
    simp only [FiniteNetwork.energy, potentialNetwork, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro edge _
    rw [renormalizationEigenpair]
    field_simp [resistanceRatePositive.ne', (resistancesPositive (network.color edge)).ne']
  refine ⟨extension, extensionOld, ?_, ?_⟩
  · rw [extensionEnergy]
    exact scaledTrace
  · intro competitor competitorOld
    rw [← scaledTrace]
    exact mul_le_mul_of_nonneg_left (lowerBound competitor competitorOld) resistanceRatePositive.le

end EIGS.Network
