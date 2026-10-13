import RequestProject.Section31.EIGSHarmonicLinear
import RequestProject.Section31.EIGSVertexInclusion

/-! Actual global finite-level minimality of the constructed stationary
weighted harmonic functions. The proof extends each finite competitor to the
union and applies the proved energy trace monotonicity. -/

namespace EIGS

open IGS.Sec31

variable {K : ℕ}

section Eigenpair

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)

include rulesConnected renormalizationEigenpair

theorem xiWeightedFiniteNetwork_iterated_restriction_le (coarseLevel offset : ℕ)
    (values : XiVtx system (coarseLevel + offset) → ℝ) :
    (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive coarseLevel).energy
      (fun vertex => values (xiForward system coarseLevel offset vertex)) ≤
    (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      (coarseLevel + offset)).energy values := by
  obtain ⟨extension, extensionValues, extensionEnergy⟩ := exists_xiHarmonic_union_extension system rulesConnected
    resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
    (coarseLevel + offset) values
  have fineAgreement : extension ∘ xiVertexEmbedding system (coarseLevel + offset) = values :=
    funext (extensionValues 0)
  have coarseAgreement : extension ∘ xiVertexEmbedding system coarseLevel =
      (fun vertex => values (xiForward system coarseLevel offset vertex)) := by
    funext vertex
    change extension (xiVertexEmbedding system coarseLevel vertex) = _
    rw [← xiVertexEmbedding_forward system coarseLevel offset vertex]
    exact extensionValues 0 (xiForward system coarseLevel offset vertex)
  have traceBound := xiUnionWeightedNetwork_energy_increasing_of_eigenpair system rulesConnected resistanceRate
    resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair extension (Nat.le_add_right coarseLevel offset)
  change (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive coarseLevel).energy
      (extension ∘ xiVertexEmbedding system coarseLevel) ≤
    (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      (coarseLevel + offset)).energy (extension ∘ xiVertexEmbedding system (coarseLevel + offset)) at traceBound
  rwa [coarseAgreement, fineAgreement] at traceBound

theorem xiHarmonicValues_initial_boundary (initialLevel offset : ℕ)
    (initialValues : XiVtx system initialLevel → ℝ) (vertex : XiVtx system initialLevel) :
    xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      renormalizationEigenpair initialLevel initialValues offset (xiForward system initialLevel offset vertex) = initialValues vertex := by
  induction offset with
  | zero => rfl
  | succ offset induction =>
      exact (xiHarmonicValues_old system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        renormalizationEigenpair initialLevel initialValues offset (xiForward system initialLevel offset vertex)).trans induction

theorem xiHarmonicValues_weighted_minimal (initialLevel offset : ℕ)
    (initialValues : XiVtx system initialLevel → ℝ) (competitor : XiVtx system (initialLevel + offset) → ℝ)
    (competitorBoundary : ∀ vertex, competitor (xiForward system initialLevel offset vertex) = initialValues vertex) :
    (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      (initialLevel + offset)).energy
      (xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        renormalizationEigenpair initialLevel initialValues offset) ≤
    (xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      (initialLevel + offset)).energy competitor := by
  rw [xiHarmonicValues_energy]
  have restrictionBound := xiWeightedFiniteNetwork_iterated_restriction_le system rulesConnected resistanceRate
    resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel offset competitor
  rwa [show (fun vertex => competitor (xiForward system initialLevel offset vertex)) = initialValues from funext competitorBoundary]
    at restrictionBound

theorem xiHarmonicValues_potential_minimal (initialLevel offset : ℕ)
    (initialValues : XiVtx system initialLevel → ℝ) (competitor : XiVtx system (initialLevel + offset) → ℝ)
    (competitorBoundary : ∀ vertex, competitor (xiForward system initialLevel offset vertex) = initialValues vertex) :
    ((XiNetwork system (initialLevel + offset)).potentialNetwork resistanceVector resistanceVectorPositive).energy
      (xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        renormalizationEigenpair initialLevel initialValues offset) ≤
    ((XiNetwork system (initialLevel + offset)).potentialNetwork resistanceVector resistanceVectorPositive).energy competitor := by
  have weightedBound := xiHarmonicValues_weighted_minimal system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel offset initialValues competitor competitorBoundary
  rw [xiWeightedFiniteNetwork_energy_eq_potential, xiWeightedFiniteNetwork_energy_eq_potential] at weightedBound
  exact le_of_mul_le_mul_left weightedBound (pow_pos resistanceRatePositive (initialLevel + offset))

end Eigenpair

end EIGS
