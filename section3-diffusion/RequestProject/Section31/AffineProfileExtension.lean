import RequestProject.Section31.SubstitutionTrace

/-! Explicit affine rule profiles give the actual substituted minimizer.
This provides the pointwise formula needed for oscillation estimates. -/

namespace EIGS.Network

open IGS.Sec31

variable {K : ℕ} (network : Network K)

theorem potential_minimum_unique
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected) (boundary : Finset network.V)
    (boundaryNonempty : boundary.Nonempty) (boundaryValues first second : network.V → ℝ)
    (firstBoundary : ∀ vertex ∈ boundary, first vertex = boundaryValues vertex)
    (secondBoundary : ∀ vertex ∈ boundary, second vertex = boundaryValues vertex)
    (firstMinimal : ∀ competitor : network.V → ℝ,
      (∀ vertex ∈ boundary, competitor vertex = boundaryValues vertex) →
      (network.potentialNetwork resistances resistancesPositive).energy first ≤
        (network.potentialNetwork resistances resistancesPositive).energy competitor)
    (secondMinimal : ∀ competitor : network.V → ℝ,
      (∀ vertex ∈ boundary, competitor vertex = boundaryValues vertex) →
      (network.potentialNetwork resistances resistancesPositive).energy second ≤
        (network.potentialNetwork resistances resistancesPositive).energy competitor) :
    first = second := by
  obtain ⟨boundaryVertex, boundaryMembership⟩ := boundaryNonempty
  obtain ⟨poincareConstant, poincareNonnegative, poincareBound⟩ :=
    network.exists_potential_poincare_constant resistances resistancesPositive boundaryVertex connected
  exact (network.potentialNetwork resistances resistancesPositive).min_unique boundary boundaryValues
    poincareConstant (fun perturbation perturbationZero vertex =>
      poincareBound perturbation (perturbationZero boundaryVertex boundaryMembership) vertex)
    first second firstBoundary secondBoundary firstMinimal secondMinimal

variable (rules : RuleFamily K)

noncomputable def substAffineProfiles (profiles : ∀ colour, (rules.R colour).V → ℝ)
    (oldValues : network.V → ℝ) : (network.subst rules).V → ℝ
  | Sum.inl vertex => oldValues vertex
  | Sum.inr privateVertex =>
      oldValues (network.head privateVertex.1) +
        (oldValues (network.tail privateVertex.1) - oldValues (network.head privateVertex.1)) *
          profiles (network.color privateVertex.1) privateVertex.2.val

theorem substAffineProfiles_restrict (profiles : ∀ colour, (rules.R colour).V → ℝ)
    (profilesPlus : ∀ colour, profiles colour (rules.βplus colour) = 1)
    (profilesMinus : ∀ colour, profiles colour (rules.βminus colour) = 0)
    (oldValues : network.V → ℝ) (edge : network.E) (vertex : (rules.R (network.color edge)).V) :
    network.substAffineProfiles rules profiles oldValues (network.substEmbed rules edge vertex) =
      oldValues (network.head edge) +
        (oldValues (network.tail edge) - oldValues (network.head edge)) * profiles (network.color edge) vertex := by
  by_cases vertexPlus : vertex = rules.βplus (network.color edge)
  · subst vertex
    simp [substEmbed, substAffineProfiles, profilesPlus]
  · by_cases vertexMinus : vertex = rules.βminus (network.color edge)
    · subst vertex
      simp [substEmbed, substAffineProfiles, vertexPlus, profilesMinus]
    · simp [substEmbed, substAffineProfiles, vertexPlus, vertexMinus]

theorem substAffineProfiles_minimal
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (profiles : ∀ colour, (rules.R colour).V → ℝ)
    (profilesPlus : ∀ colour, profiles colour (rules.βplus colour) = 1)
    (profilesMinus : ∀ colour, profiles colour (rules.βminus colour) = 0)
    (profilesMinimal : ∀ colour (competitor : (rules.R colour).V → ℝ),
      competitor (rules.βplus colour) = 1 → competitor (rules.βminus colour) = 0 →
      ((rules.R colour).potentialNetwork resistances resistancesPositive).energy (profiles colour) ≤
        ((rules.R colour).potentialNetwork resistances resistancesPositive).energy competitor)
    (oldValues : network.V → ℝ) :
    ∀ competitor : (network.subst rules).V → ℝ,
      (∀ vertex, competitor (Sum.inl vertex) = oldValues vertex) →
      ((network.subst rules).potentialNetwork resistances resistancesPositive).energy
        (network.substAffineProfiles rules profiles oldValues) ≤
        ((network.subst rules).potentialNetwork resistances resistancesPositive).energy competitor := by
  classical
  intro competitor competitorOld
  rw [network.substituted_potential_energy_eq_sum, network.substituted_potential_energy_eq_sum]
  apply Finset.sum_le_sum
  intro edge _
  have restrictionEquality :
      (fun vertex => network.substAffineProfiles rules profiles oldValues (network.substEmbed rules edge vertex)) =
      (fun vertex => oldValues (network.head edge) +
        (oldValues (network.tail edge) - oldValues (network.head edge)) * profiles (network.color edge) vertex) :=
    funext (network.substAffineProfiles_restrict rules profiles profilesPlus profilesMinus oldValues edge)
  rw [restrictionEquality]
  apply ((rules.R (network.color edge)).potentialNetwork resistances resistancesPositive).min_affine
    {rules.βplus (network.color edge), rules.βminus (network.color edge)}
    (profiles (network.color edge)) (profiles (network.color edge)) (oldValues (network.head edge))
    (oldValues (network.tail edge) - oldValues (network.head edge))
  · intro trial trialBoundary
    apply profilesMinimal (network.color edge) trial
    · simpa [profilesPlus] using trialBoundary (rules.βplus (network.color edge)) (by simp)
    · simpa [profilesMinus] using trialBoundary (rules.βminus (network.color edge)) (by simp)
  · intro vertex membership
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using membership :
      vertex = rules.βplus (network.color edge) ∨ vertex = rules.βminus (network.color edge)) with
      vertexPlus | vertexMinus
    · subst vertex
      simp [substEmbed, profilesPlus, competitorOld]
    · subst vertex
      simp [substEmbed, profilesMinus, competitorOld, (rules.plant_ne (network.color edge)).symm]

theorem substAffineProfiles_edge_difference (profiles : ∀ colour, (rules.R colour).V → ℝ)
    (profilesPlus : ∀ colour, profiles colour (rules.βplus colour) = 1)
    (profilesMinus : ∀ colour, profiles colour (rules.βminus colour) = 0)
    (oldValues : network.V → ℝ) (edge : (network.subst rules).E) :
    network.substAffineProfiles rules profiles oldValues ((network.subst rules).tail edge) -
        network.substAffineProfiles rules profiles oldValues ((network.subst rules).head edge) =
      (oldValues (network.tail edge.1) - oldValues (network.head edge.1)) *
        (profiles (network.color edge.1) ((rules.R (network.color edge.1)).tail edge.2) -
          profiles (network.color edge.1) ((rules.R (network.color edge.1)).head edge.2)) := by
  change network.substAffineProfiles rules profiles oldValues
      (network.substEmbed rules edge.1 ((rules.R (network.color edge.1)).tail edge.2)) -
    network.substAffineProfiles rules profiles oldValues
      (network.substEmbed rules edge.1 ((rules.R (network.color edge.1)).head edge.2)) = _
  rw [network.substAffineProfiles_restrict rules profiles profilesPlus profilesMinus,
    network.substAffineProfiles_restrict rules profiles profilesPlus profilesMinus]
  ring

end EIGS.Network
