import RequestProject.Section2GroundedTrace
import RequestProject.Section2ResistanceSpectralRadius

/-! Effective resistance between arbitrary distinct persistent vertices.
Only the selected sink is grounded. All other coarse vertices remain free;
the iterated trace minimization supplies both comparisons. -/

namespace EIGS
noncomputable section
open scoped BigOperators Classical
open IGS.Sec31
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem Network.potential_energy_bounds_of_resistance_bounds (network : Network K)
    (resistances : Fin K → ℝ) (positive : ∀ colour, 0 < resistances colour)
    (lower upper : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (bounds : ∀ colour, lower ≤ resistances colour ∧ resistances colour ≤ upper)
    (values : network.V → ℝ) :
    upper⁻¹ * (network.potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy values ≤
      (network.potentialNetwork resistances positive).energy values ∧
    (network.potentialNetwork resistances positive).energy values ≤
      lower⁻¹ * (network.potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy values := by
  change upper⁻¹ * (∑ edge, (1 : ℝ)⁻¹ * (values (network.tail edge) - values (network.head edge)) ^ 2) ≤
      (∑ edge, (resistances (network.color edge))⁻¹ * (values (network.tail edge) - values (network.head edge)) ^ 2) ∧
    (∑ edge, (resistances (network.color edge))⁻¹ * (values (network.tail edge) - values (network.head edge)) ^ 2) ≤
      lower⁻¹ * (∑ edge, (1 : ℝ)⁻¹ * (values (network.tail edge) - values (network.head edge)) ^ 2)
  simp only [inv_one, one_mul, Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro edge _
    exact mul_le_mul_of_nonneg_right
      ((inv_le_inv₀ upperPositive (positive (network.color edge))).mpr (bounds (network.color edge)).2)
      (sq_nonneg _)
  · apply Finset.sum_le_sum
    intro edge _
    exact mul_le_mul_of_nonneg_right
      ((inv_le_inv₀ (positive (network.color edge)) lowerPositive).mpr (bounds (network.color edge)).1)
      (sq_nonneg _)

theorem xiSimpleGraph_fixed_pair_resistance_comparison (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (coarse steps : ℕ) (source sink : XiVtx system coarse) (distinct : source ≠ sink)
    (lower upper : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (bounds : ∀ colour, lower ≤ (system.ruleFamily connected).Psi^[steps] (fun _ => 1) colour ∧
      (system.ruleFamily connected).Psi^[steps] (fun _ => 1) colour ≤ upper) :
    lower * effResToBoundary (XiSimpleGraph system coarse) (Finset.univ.erase sink) source ≤
      effResToBoundary (XiSimpleGraph system (coarse + steps))
        (Finset.univ.erase (xiForward system coarse steps sink)) (xiForward system coarse steps source) ∧
    effResToBoundary (XiSimpleGraph system (coarse + steps))
        (Finset.univ.erase (xiForward system coarse steps sink)) (xiForward system coarse steps source) ≤
      upper * effResToBoundary (XiSimpleGraph system coarse) (Finset.univ.erase sink) source := by
  classical
  let coarseGraph := XiSimpleGraph system coarse
  let fineGraph := XiSimpleGraph system (coarse + steps)
  let coarseDomain := Finset.univ.erase sink
  let fineDomain := Finset.univ.erase (xiForward system coarse steps sink)
  have coarseConnected : coarseGraph.Connected := xiSimpleGraph_connected system connected coarse
  have fineConnected : fineGraph.Connected := xiSimpleGraph_connected system connected (coarse + steps)
  have coarseComplement : coarseDomainᶜ.Nonempty := ⟨sink, by simp [coarseDomain]⟩
  have fineComplement : fineDomainᶜ.Nonempty := ⟨xiForward system coarse steps sink, by simp [fineDomain]⟩
  have coarseInside : source ∈ coarseDomain := by simp [coarseDomain, distinct]
  have fineDistinct : xiForward system coarse steps source ≠ xiForward system coarse steps sink :=
    fun equality => distinct ((xiForward_injective system coarse steps) equality)
  have fineInside : xiForward system coarse steps source ∈ fineDomain := by simp [fineDomain, fineDistinct]
  let coarseResistance := effResToBoundary coarseGraph coarseDomain source
  let fineResistance := effResToBoundary fineGraph fineDomain (xiForward system coarse steps source)
  have coarsePositive : 0 < coarseResistance :=
    effResToBoundary_pos coarseGraph coarseConnected coarseComplement coarseInside
  have finePositive : 0 < fineResistance :=
    effResToBoundary_pos fineGraph fineConnected fineComplement fineInside
  let coarseVoltage := boundaryVoltageProfile coarseGraph coarseDomain source
  let fineVoltage := boundaryVoltageProfile fineGraph fineDomain (xiForward system coarse steps source)
  have coarseSource : coarseVoltage source = 1 :=
    boundaryVoltageProfile_source coarseGraph coarseConnected coarseComplement coarseInside
  have coarseSink : coarseVoltage sink = 0 := boundaryVoltageProfile_zero coarseGraph (by simp [coarseDomain])
  have fineSource : fineVoltage (xiForward system coarse steps source) = 1 :=
    boundaryVoltageProfile_source fineGraph fineConnected fineComplement fineInside
  have fineSink : fineVoltage (xiForward system coarse steps sink) = 0 :=
    boundaryVoltageProfile_zero fineGraph (by simp [fineDomain])
  have coarseEnergy : dirichletEnergy coarseGraph coarseVoltage = coarseResistance⁻¹ :=
    boundaryVoltageProfile_energy coarseGraph coarseConnected coarseComplement coarseInside
  have fineEnergy : dirichletEnergy fineGraph fineVoltage = fineResistance⁻¹ :=
    boundaryVoltageProfile_energy fineGraph fineConnected fineComplement fineInside
  have coarseUnit (values : XiVtx system coarse → ℝ) :
      ((XiNetwork system coarse).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy values =
        dirichletEnergy coarseGraph values :=
    (XiNetwork system coarse).unit_potential_energy_eq_dirichletEnergy
      (xiNetwork_loopless system connected loopless coarse)
      (xiNetwork_edges_unique system connected loopless unique plantingNonadjacent coarse) values
  have fineUnit (values : XiVtx system (coarse + steps) → ℝ) :
      ((XiNetwork system (coarse + steps)).potentialNetwork (fun _ => 1) (fun _ => by norm_num)).energy values =
        dirichletEnergy fineGraph values :=
    (XiNetwork system (coarse + steps)).unit_potential_energy_eq_dirichletEnergy
      (xiNetwork_loopless system connected loopless (coarse + steps))
      (xiNetwork_edges_unique system connected loopless unique plantingNonadjacent (coarse + steps)) values
  let resistances := (system.ruleFamily connected).Psi^[steps] (fun _ => 1)
  have resistancesPositive : ∀ colour, 0 < resistances colour :=
    ruleFamily_Psi_iterate_positive system connected (fun _ => 1) (fun _ => by norm_num) steps
  obtain ⟨extension, extensionOld, extensionEnergy, _⟩ :=
    exists_xiUnit_iterated_trace system connected coarse steps coarseVoltage
  have extensionSource : extension (xiForward system coarse steps source) = 1 :=
    (extensionOld source).trans coarseSource
  have extensionZero : ∀ point, point ∉ fineDomain → extension point = 0 := by
    intro point outside
    have equality : point = xiForward system coarse steps sink := by simpa [fineDomain] using outside
    subst point
    exact (extensionOld sink).trans coarseSink
  have fineMinimum := boundaryVoltageProfile_minimum fineGraph fineConnected fineComplement fineInside
    extension extensionSource extensionZero
  rw [fineEnergy, ← fineUnit extension, extensionEnergy] at fineMinimum
  have upperEnergy := ((XiNetwork system coarse).potential_energy_bounds_of_resistance_bounds
    resistances resistancesPositive lower upper lowerPositive upperPositive bounds coarseVoltage).2
  rw [coarseUnit coarseVoltage, coarseEnergy] at upperEnergy
  have fineCapacityUpper : fineResistance⁻¹ ≤ lower⁻¹ * coarseResistance⁻¹ := fineMinimum.trans upperEnergy
  let restricted := fun point : XiVtx system coarse => fineVoltage (xiForward system coarse steps point)
  have restrictedSource : restricted source = 1 := fineSource
  have restrictedZero : ∀ point, point ∉ coarseDomain → restricted point = 0 := by
    intro point outside
    have equality : point = sink := by simpa [coarseDomain] using outside
    subst point
    exact fineSink
  have coarseMinimum := boundaryVoltageProfile_minimum coarseGraph coarseConnected coarseComplement coarseInside
    restricted restrictedSource restrictedZero
  rw [coarseEnergy] at coarseMinimum
  have restrictionEnergy := xiPotential_iterated_restriction_le system connected coarse steps
    (fun _ => 1) (fun _ => by norm_num) fineVoltage
  rw [fineUnit fineVoltage, fineEnergy] at restrictionEnergy
  have lowerEnergy := ((XiNetwork system coarse).potential_energy_bounds_of_resistance_bounds
    resistances resistancesPositive lower upper lowerPositive upperPositive bounds restricted).1
  rw [coarseUnit restricted] at lowerEnergy
  have fineCapacityLower : upper⁻¹ * coarseResistance⁻¹ ≤ fineResistance⁻¹ :=
    (mul_le_mul_of_nonneg_left coarseMinimum (inv_nonneg.mpr upperPositive.le)).trans
      (lowerEnergy.trans restrictionEnergy)
  constructor
  · apply (inv_le_inv₀ finePositive (mul_pos lowerPositive coarsePositive)).mp
    simpa only [mul_inv_rev, mul_comm] using fineCapacityUpper
  · apply (inv_le_inv₀ (mul_pos upperPositive coarsePositive) finePositive).mp
    simpa only [mul_inv_rev, mul_comm] using fineCapacityLower

theorem xiSimpleGraph_fixed_pair_resistance_canonical_bounds (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (coarse : ℕ) (source sink : XiVtx system coarse) (distinct : source ≠ sink) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ steps,
      lower * (system.resistanceSpectralRadius connected distancePositive) ^ steps ≤
        effResToBoundary (XiSimpleGraph system (coarse + steps))
          (Finset.univ.erase (xiForward system coarse steps sink)) (xiForward system coarse steps source) ∧
      effResToBoundary (XiSimpleGraph system (coarse + steps))
          (Finset.univ.erase (xiForward system coarse steps sink)) (xiForward system coarse steps source) ≤
        upper * (system.resistanceSpectralRadius connected distancePositive) ^ steps := by
  classical
  obtain ⟨lower, upper, lowerPositive, upperPositive, bounds⟩ :=
    system.resistanceSpectralRadius_iterate_bounds connected distancePositive
  have coarsePositive : 0 < effResToBoundary (XiSimpleGraph system coarse) (Finset.univ.erase sink) source :=
    effResToBoundary_pos _ (xiSimpleGraph_connected system connected coarse)
      ⟨sink, by simp⟩ (by simp [distinct])
  have ratePositive := (system.resistanceSpectralRadius_positive_eigenpair connected distancePositive).1
  refine ⟨lower * _, upper * _, mul_pos lowerPositive coarsePositive, mul_pos upperPositive coarsePositive, ?_⟩
  intro steps
  have comparison := xiSimpleGraph_fixed_pair_resistance_comparison system connected loopless unique
    plantingNonadjacent coarse steps source sink distinct
    (lower * (system.resistanceSpectralRadius connected distancePositive) ^ steps)
    (upper * (system.resistanceSpectralRadius connected distancePositive) ^ steps)
    (mul_pos lowerPositive (pow_pos ratePositive steps))
    (mul_pos upperPositive (pow_pos ratePositive steps)) (bounds steps)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using comparison

end
end EIGS

#print axioms EIGS.Network.potential_energy_bounds_of_resistance_bounds
#print axioms EIGS.xiSimpleGraph_fixed_pair_resistance_comparison
#print axioms EIGS.xiSimpleGraph_fixed_pair_resistance_canonical_bounds
