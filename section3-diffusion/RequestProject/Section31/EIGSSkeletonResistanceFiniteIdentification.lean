import RequestProject.Section31.EIGSSkeletonResistanceTriangle
import RequestProject.Section31.EIGSEnergyConstantsQuotient
import RequestProject.Section31.EIGSHarmonicExtension
import RequestProject.Section31.DirichletThomson

/-! Prepared outside the repository during the snapshot freeze. Actual
skeleton resistance equals the scaled finite-network effective resistance
whenever the two vertices belong to that finite level. Both inequalities use
actual attained finite Dirichlet minima and exact harmonic union extension.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31
noncomputable section
variable {K : ℕ}

theorem xiSkeletonResistance_eq_finite_effRes
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (anchor : XiVertexUnion system) (level : ℕ)
    (source sink : XiVtx system level) (distinct : source ≠ sink) :
    xiSkeletonResistance system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor (xiVertexEmbedding system level source) (xiVertexEmbedding system level sink) =
    (XiNetwork system level).effRes source sink
      ((XiNetwork system level).flow_nonempty_of_connected
        (xiSimpleGraph_connected system rulesConnected level) source sink distinct) resistanceVector /
      resistanceRate ^ level := by
  let finiteResistance := (XiNetwork system level).effRes source sink
    ((XiNetwork system level).flow_nonempty_of_connected
      (xiSimpleGraph_connected system rulesConnected level) source sink distinct) resistanceVector
  let resistance := xiSkeletonResistance system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
    eigenpair anchor (xiVertexEmbedding system level source) (xiVertexEmbedding system level sink)
  obtain ⟨potential, sourceValue, sinkValue, minimal, potentialEnergy⟩ :=
    (XiNetwork system level).exists_minimum_potential_energy_eq_inverse_effRes resistanceVector vectorPositive
      (xiSimpleGraph_connected system rulesConnected level) source sink distinct
  have potentialPositive := (XiNetwork system level).potential_energy_pos_of_boundary_unit
    resistanceVector vectorPositive source sink distinct
    ((XiNetwork system level).flow_nonempty_of_connected
      (xiSimpleGraph_connected system rulesConnected level) source sink distinct)
    potential sourceValue sinkValue
  have finiteResistancePositive : 0 < finiteResistance := by
    rw [potentialEnergy] at potentialPositive
    exact inv_pos.mp potentialPositive
  obtain ⟨extension, extensionValues, extensionEnergy⟩ := exists_xiHarmonic_union_extension system rulesConnected
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair level potential
  have extensionFinite : extension ∈ xiWeightedEnergyDomain system resistanceRate ratePositive
      resistanceVector vectorPositive := by
    apply (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive extension).2
    rw [extensionEnergy]
    exact ENNReal.ofReal_ne_top
  obtain ⟨normalized, normalizedProperty, _⟩ := exists_unique_xiEnergy_zero_anchored_representative
    system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive anchor eigenpair
    ⟨extension, extensionFinite⟩
  have normalizedDifference : normalized.val.value.val (xiVertexEmbedding system level source) -
      normalized.val.value.val (xiVertexEmbedding system level sink) = 1 := by
    rw [normalizedProperty.1, normalizedProperty.1, extensionValues 0 source, extensionValues 0 sink]
    change potential source - extension anchor - (potential sink - extension anchor) = 1
    rw [sourceValue, sinkValue]
    ring
  have extensionEnergyValue : (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector
      vectorPositive extension).toReal = resistanceRate ^ level * finiteResistance⁻¹ := by
    rw [extensionEnergy, ENNReal.toReal_ofReal (FiniteNetwork.energy_nonneg _ _),
      xiWeightedFiniteNetwork_energy_eq_potential, potentialEnergy]
  have lower := xiSkeletonResistance_sharp_energy_bound system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair anchor (xiVertexEmbedding system level source)
    (xiVertexEmbedding system level sink) normalized
  rw [normalizedDifference, ← xiZeroAnchoredEnergyDomain_norm_sq, normalizedProperty.2,
    extensionEnergyValue] at lower
  change (1 : ℝ) ^ 2 ≤ resistance * (resistanceRate ^ level * finiteResistance⁻¹) at lower
  norm_num only [one_pow] at lower
  have resistanceNonnegative : 0 ≤ resistance := sq_nonneg _
  have resistancePositive : 0 < resistance := by
    by_contra notPositive
    have zero : resistance = 0 := le_antisymm (not_lt.mp notPositive) resistanceNonnegative
    simp only [zero, zero_mul] at lower
    norm_num at lower
  have lowerDiv : 1 ≤ (resistance * resistanceRate ^ level) / finiteResistance := by
    convert lower using 1 <;> ring
  have lowerScaled : finiteResistance ≤ resistance * resistanceRate ^ level := by
    simpa only [one_mul] using (le_div_iff₀ finiteResistancePositive).1 lowerDiv
  let representative := xiSkeletonResistanceRiesz system rulesConnected resistanceRate ratePositive resistanceVector
    vectorPositive eigenpair anchor (xiVertexEmbedding system level source) (xiVertexEmbedding system level sink)
  let restricted := representative.val.value.val ∘ xiVertexEmbedding system level
  have representativeDifference : restricted source - restricted sink = resistance :=
    xiSkeletonResistanceRiesz_attains system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor (xiVertexEmbedding system level source) (xiVertexEmbedding system level sink)
  obtain ⟨finiteMinimizer, _, _, finiteMinimal, finiteMinimumEnergy⟩ :=
    (XiNetwork system level).exists_minimum_potential_energy_terminal_values resistanceVector vectorPositive
      (xiSimpleGraph_connected system rulesConnected level) source sink distinct (restricted source) (restricted sink)
  have minimumBound := finiteMinimal restricted rfl rfl
  rw [finiteMinimumEnergy, representativeDifference] at minimumBound
  have finiteBound := finite_energy_le_traceEnergyValue
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
    representative.val.value level
  change (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
    restricted ≤ (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      representative.val.value.val).toReal at finiteBound
  have representativeEnergy : (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector
      vectorPositive representative.val.value.val).toReal = resistance :=
    (xiZeroAnchoredEnergyDomain_norm_sq system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair anchor representative).symm
  rw [xiWeightedFiniteNetwork_energy_eq_potential, representativeEnergy] at finiteBound
  have scaledMinimum := (mul_le_mul_of_nonneg_left minimumBound (pow_pos ratePositive level).le).trans finiteBound
  have upperDiv : resistanceRate ^ level * resistance ^ 2 / finiteResistance ≤ resistance := by
    convert scaledMinimum using 1 <;> ring
  have upperScaled := (div_le_iff₀ finiteResistancePositive).1 upperDiv
  have upperProduct : resistance * (resistance * resistanceRate ^ level) ≤ resistance * finiteResistance := by
    nlinarith [upperScaled]
  have upper : resistance * resistanceRate ^ level ≤ finiteResistance :=
    (mul_le_mul_left resistancePositive).1 upperProduct
  apply (eq_div_iff (pow_pos ratePositive level).ne').2
  exact le_antisymm upper lowerScaled

end
end EIGS

#print axioms EIGS.xiSkeletonResistance_eq_finite_effRes
