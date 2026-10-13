import RequestProject.Section31.EIGSDiscreteTraceProfiles

/-! Algebra of the actual finite Dirichlet minimizers. Multiplying every
resistance by the same positive constant leaves the minimizer unchanged;
harmonic extension is linear because of the proved energy orthogonality. -/

namespace EIGS.Network

open IGS.Sec31

variable {K : ℕ} (network : Network K)

theorem potential_energy_resistance_mul
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (scalar : ℝ) (scalarPositive : 0 < scalar) (values : network.V → ℝ) :
    (network.potentialNetwork (fun colour => scalar * resistances colour)
      (fun colour => mul_pos scalarPositive (positive colour))).energy values =
      scalar⁻¹ * (network.potentialNetwork resistances positive).energy values := by
  simp only [FiniteNetwork.energy, potentialNetwork, mul_inv_rev, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem boundaryPotentialProfile_resistance_mul
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (scalar : ℝ) (scalarPositive : 0 < scalar)
    (connected : network.toSimpleGraph.Connected)
    (boundary : Finset network.V) (boundaryNonempty : boundary.Nonempty)
    (boundaryValues : network.V → ℝ) :
    network.boundaryPotentialProfile (fun colour => scalar * resistances colour)
        (fun colour => mul_pos scalarPositive (positive colour)) connected boundary boundaryNonempty boundaryValues =
      network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty boundaryValues := by
  apply network.potential_minimum_unique (fun colour => scalar * resistances colour)
    (fun colour => mul_pos scalarPositive (positive colour)) connected boundary boundaryNonempty boundaryValues
  · exact network.boundaryPotentialProfile_boundary _ _ connected boundary boundaryNonempty boundaryValues
  · exact network.boundaryPotentialProfile_boundary _ _ connected boundary boundaryNonempty boundaryValues
  · exact network.boundaryPotentialProfile_minimal _ _ connected boundary boundaryNonempty boundaryValues
  · intro competitor competitorBoundary
    rw [network.potential_energy_resistance_mul resistances positive scalar scalarPositive,
      network.potential_energy_resistance_mul resistances positive scalar scalarPositive]
    exact mul_le_mul_of_nonneg_left
      (network.boundaryPotentialProfile_minimal resistances positive connected boundary boundaryNonempty
        boundaryValues competitor competitorBoundary) (inv_pos.2 scalarPositive).le

theorem boundaryPotentialProfile_linear
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected)
    (boundary : Finset network.V) (boundaryNonempty : boundary.Nonempty)
    (firstValues secondValues : network.V → ℝ) (firstScalar secondScalar : ℝ) :
    network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty
        (fun vertex => firstScalar * firstValues vertex + secondScalar * secondValues vertex) =
      (fun vertex => firstScalar * network.boundaryPotentialProfile resistances positive connected
          boundary boundaryNonempty firstValues vertex +
        secondScalar * network.boundaryPotentialProfile resistances positive connected
          boundary boundaryNonempty secondValues vertex) := by
  have linearBoundary : ∀ vertex ∈ boundary,
      firstScalar * network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty firstValues vertex +
        secondScalar * network.boundaryPotentialProfile resistances positive connected boundary boundaryNonempty secondValues vertex =
      firstScalar * firstValues vertex + secondScalar * secondValues vertex := by
    intro vertex membership
    rw [network.boundaryPotentialProfile_boundary _ _ connected boundary boundaryNonempty firstValues vertex membership,
      network.boundaryPotentialProfile_boundary _ _ connected boundary boundaryNonempty secondValues vertex membership]
  apply network.potential_minimum_unique resistances positive connected boundary boundaryNonempty
    (fun vertex => firstScalar * firstValues vertex + secondScalar * secondValues vertex)
  · exact network.boundaryPotentialProfile_boundary _ _ connected boundary boundaryNonempty _
  · exact linearBoundary
  · exact network.boundaryPotentialProfile_minimal _ _ connected boundary boundaryNonempty _
  · apply (network.potentialNetwork resistances positive).minimum_of_energyInner_vanishes
      (↑boundary : Set network.V) _ _ linearBoundary
    intro perturbation perturbationBoundary
    rw [FiniteNetwork.energyInner_linear_first]
    have firstOrthogonality := (network.potentialNetwork resistances positive).energyInner_eq_zero_of_min
      (↑boundary : Set network.V) firstValues _
      (network.boundaryPotentialProfile_boundary _ _ connected boundary boundaryNonempty firstValues)
      (network.boundaryPotentialProfile_minimal _ _ connected boundary boundaryNonempty firstValues)
      perturbation perturbationBoundary
    have secondOrthogonality := (network.potentialNetwork resistances positive).energyInner_eq_zero_of_min
      (↑boundary : Set network.V) secondValues _
      (network.boundaryPotentialProfile_boundary _ _ connected boundary boundaryNonempty secondValues)
      (network.boundaryPotentialProfile_minimal _ _ connected boundary boundaryNonempty secondValues)
      perturbation perturbationBoundary
    rw [firstOrthogonality, secondOrthogonality]
    ring

end EIGS.Network
