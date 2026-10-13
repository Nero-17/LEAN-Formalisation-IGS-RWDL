import RequestProject.Section31.Oscillation

/-!
# Energy orthogonality of finite harmonic minimizers

The scalar product below is the edge-energy bilinear form. It is unrelated to
an L² projection. Harmonic minimization implies its orthogonality to every
zero-boundary perturbation and gives the exact Pythagorean energy identity.
-/

namespace IGS.Sec31.FiniteNetwork

variable {Vertex : Type*} (network : FiniteNetwork Vertex)

noncomputable def energyInner (first second : Vertex → ℝ) : ℝ :=
  ∑ edge, network.cond edge *
    (first (network.ends edge).1 - first (network.ends edge).2) *
      (second (network.ends edge).1 - second (network.ends edge).2)

theorem energy_line (first second : Vertex → ℝ) (parameter : ℝ) :
    network.energy (fun vertex => first vertex + parameter * second vertex) =
      network.energy first + 2 * parameter * network.energyInner first second +
        parameter ^ 2 * network.energy second := by
  simp only [energy, energyInner, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem energyInner_eq_zero_of_min (boundary : Set Vertex)
    (boundaryValues potential : Vertex → ℝ)
    (potentialBoundary : ∀ vertex ∈ boundary, potential vertex = boundaryValues vertex)
    (potentialMinimal : ∀ competitor : Vertex → ℝ,
      (∀ vertex ∈ boundary, competitor vertex = boundaryValues vertex) →
        network.energy potential ≤ network.energy competitor)
    (perturbation : Vertex → ℝ)
    (perturbationVanishes : ∀ vertex ∈ boundary, perturbation vertex = 0) :
    network.energyInner potential perturbation = 0 := by
  apply eq_zero_of_quadratic_nonneg _ _ (network.energy_nonneg perturbation)
  intro parameter
  have comparison := potentialMinimal (fun vertex => potential vertex + parameter * perturbation vertex)
    (fun vertex membership => by simp [potentialBoundary vertex membership,
      perturbationVanishes vertex membership])
  rw [network.energy_line] at comparison
  linarith

theorem energy_add_of_min (boundary : Set Vertex)
    (boundaryValues potential : Vertex → ℝ)
    (potentialBoundary : ∀ vertex ∈ boundary, potential vertex = boundaryValues vertex)
    (potentialMinimal : ∀ competitor : Vertex → ℝ,
      (∀ vertex ∈ boundary, competitor vertex = boundaryValues vertex) →
        network.energy potential ≤ network.energy competitor)
    (perturbation : Vertex → ℝ)
    (perturbationVanishes : ∀ vertex ∈ boundary, perturbation vertex = 0) :
    network.energy (potential + perturbation) = network.energy potential + network.energy perturbation := by
  have orthogonality := network.energyInner_eq_zero_of_min boundary boundaryValues potential
    potentialBoundary potentialMinimal perturbation perturbationVanishes
  simpa only [one_mul, one_pow, orthogonality, mul_zero, add_zero] using
    network.energy_line potential perturbation 1

theorem energy_sub_of_min (boundary : Set Vertex)
    (boundaryValues potential : Vertex → ℝ)
    (potentialBoundary : ∀ vertex ∈ boundary, potential vertex = boundaryValues vertex)
    (potentialMinimal : ∀ competitor : Vertex → ℝ,
      (∀ vertex ∈ boundary, competitor vertex = boundaryValues vertex) →
        network.energy potential ≤ network.energy competitor)
    (competitor : Vertex → ℝ)
    (competitorBoundary : ∀ vertex ∈ boundary, competitor vertex = boundaryValues vertex) :
    network.energy competitor = network.energy potential + network.energy (competitor - potential) := by
  have perturbationVanishes : ∀ vertex ∈ boundary, (competitor - potential) vertex = 0 := by
    intro vertex membership
    simp [competitorBoundary vertex membership, potentialBoundary vertex membership]
  simpa only [add_sub_cancel] using network.energy_add_of_min boundary boundaryValues potential
    potentialBoundary potentialMinimal (competitor - potential) perturbationVanishes

theorem energyInner_linear_first (first second perturbation : Vertex → ℝ) (firstScalar secondScalar : ℝ) :
    network.energyInner (fun vertex => firstScalar * first vertex + secondScalar * second vertex) perturbation =
      firstScalar * network.energyInner first perturbation +
        secondScalar * network.energyInner second perturbation := by
  simp only [energyInner, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem minimum_of_energyInner_vanishes (boundary : Set Vertex)
    (boundaryValues potential : Vertex → ℝ)
    (potentialBoundary : ∀ vertex ∈ boundary, potential vertex = boundaryValues vertex)
    (potentialOrthogonal : ∀ perturbation : Vertex → ℝ,
      (∀ vertex ∈ boundary, perturbation vertex = 0) → network.energyInner potential perturbation = 0) :
    ∀ competitor : Vertex → ℝ,
      (∀ vertex ∈ boundary, competitor vertex = boundaryValues vertex) →
        network.energy potential ≤ network.energy competitor := by
  intro competitor competitorBoundary
  have orthogonality := potentialOrthogonal (competitor - potential) (by
    intro vertex membership
    simp [competitorBoundary vertex membership, potentialBoundary vertex membership])
  have decomposition := network.energy_line potential (competitor - potential) 1
  have energyNonnegative := network.energy_nonneg (competitor - potential)
  simp only [one_mul, one_pow, orthogonality, mul_zero, add_zero] at decomposition
  have functionsEqual : (fun vertex => potential vertex + (competitor - potential) vertex) = competitor := by
    funext vertex
    simp
  rw [functionsEqual] at decomposition
  linarith

end IGS.Sec31.FiniteNetwork
