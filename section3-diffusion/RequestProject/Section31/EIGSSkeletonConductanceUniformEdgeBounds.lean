import RequestProject.Section31.EIGSRuleConductanceJumpBound
import RequestProject.Section31.EIGSSkeletonConductance

/-! Actual normalized coarse conductances have uniform edge lower bounds
and uniform entry upper bounds independent of coarse cardinality. The latter
uses the proved absence of parallel unoriented edges. Candidate source. -/

namespace EIGS.Network
open scoped Classical BigOperators
noncomputable section
variable {K : ℕ}

theorem unique_endpoint_weight_sum_le (network : EIGS.Network K) (unique : network.EdgesUnique)
    (weight : network.E → ℝ) (upper : ℝ) (upperNonnegative : 0 ≤ upper)
    (weightUpper : ∀ edge, weight edge ≤ upper) (source target : network.V) :
    (∑ edge : network.E,
      if (network.tail edge = source ∧ network.head edge = target) ∨
          (network.tail edge = target ∧ network.head edge = source) then weight edge else 0) ≤ upper := by
  by_cases existsEdge : ∃ edge : network.E,
      (network.tail edge = source ∧ network.head edge = target) ∨
        (network.tail edge = target ∧ network.head edge = source)
  · obtain ⟨edge, endpoints⟩ := existsEdge
    have otherEndpoints : ∀ other : network.E, other ≠ edge →
        ¬ ((network.tail other = source ∧ network.head other = target) ∨
          (network.tail other = target ∧ network.head other = source)) := by
      intro other different otherMatches
      apply different
      apply unique other edge
      rcases otherMatches with ⟨first, second⟩ | ⟨first, second⟩ <;>
        rcases endpoints with ⟨third, fourth⟩ | ⟨third, fourth⟩ <;> aesop
    rw [Finset.sum_eq_single edge]
    · simpa only [if_pos endpoints] using weightUpper edge
    · intro other _ different
      exact if_neg (otherEndpoints other different)
    · simp
  · have allZero : ∀ edge : network.E,
        (if (network.tail edge = source ∧ network.head edge = target) ∨
          (network.tail edge = target ∧ network.head edge = source) then weight edge else 0) = 0 := by
      intro edge
      exact if_neg (fun endpoints => existsEdge ⟨edge, endpoints⟩)
    simp only [allZero, Finset.sum_const_zero]
    exact upperNonnegative

end
end EIGS.Network

namespace EIGS
open IGS.Sec31
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def xiNormalizedSkeletonConductance (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (coarse steps : ℕ) (source target : XiVtx system coarse) : ℝ :=
  (system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps *
    xiSkeletonConductance system rulesConnected coarse steps source target

theorem exists_xiNormalizedSkeletonConductance_edge_bounds (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      (∀ coarse steps source target,
        xiNormalizedSkeletonConductance system rulesConnected distancePositive coarse steps source target ≤ upper) ∧
      (∀ coarse steps source target, (XiSimpleGraph system coarse).Adj source target →
        lower ≤ xiNormalizedSkeletonConductance system rulesConnected distancePositive coarse steps source target) := by
  obtain ⟨resistanceLower, resistanceUpper, lowerPositive, upperPositive, resistanceBounds⟩ :=
    system.resistanceSpectralRadius_iterate_bounds rulesConnected distancePositive
  have ratePositive := (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
  have edgeBounds (steps : ℕ) (colour : Fin K) :
      1 / resistanceUpper ≤ (system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps *
        (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1)) colour)⁻¹ ∧
      (system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps *
        (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1)) colour)⁻¹ ≤ 1 / resistanceLower := by
    have resistancePositive := ruleFamily_Psi_iterate_positive system rulesConnected
      (fun _ => 1) (fun _ => by norm_num) steps colour
    constructor
    · rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀ upperPositive resistancePositive).mpr
      nlinarith [(resistanceBounds steps colour).2]
    · rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀ resistancePositive lowerPositive).mpr
      nlinarith [(resistanceBounds steps colour).1]
  refine ⟨1 / resistanceUpper, 1 / resistanceLower, by positivity, by positivity, ?_, ?_⟩
  · intro coarse steps source target
    unfold xiNormalizedSkeletonConductance xiSkeletonConductance
    rw [Finset.mul_sum]
    simp_rw [mul_ite, mul_zero]
    exact Network.unique_endpoint_weight_sum_le (XiNetwork system coarse)
      (xiNetwork_edges_unique system rulesConnected rulesLoopless rulesUnique plantingNonadjacent coarse)
      (fun edge => (system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps *
        (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1)) (XiCol system.toRuleData coarse edge))⁻¹)
      (1 / resistanceLower) (by positivity) (fun edge => (edgeBounds steps _).2) source target
  · intro coarse steps source target adjacent
    change (XiNetwork system coarse).toSimpleGraph.Adj source target at adjacent
    obtain ⟨edge, endpoints⟩ : ∃ edge : XiEdge system.toRuleData coarse,
        (XiTail system coarse edge = source ∧ XiHead system coarse edge = target) ∨
          (XiTail system coarse edge = target ∧ XiHead system coarse edge = source) := by
      rcases adjacent.2 with ⟨edge, first, second⟩ | ⟨edge, first, second⟩
      · exact ⟨edge, Or.inl ⟨first, second⟩⟩
      · exact ⟨edge, Or.inr ⟨first, second⟩⟩
    apply (edgeBounds steps (XiCol system.toRuleData coarse edge)).1.trans
    unfold xiNormalizedSkeletonConductance xiSkeletonConductance
    rw [Finset.mul_sum]
    have bound := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun candidate : XiEdge system.toRuleData coarse =>
        (system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps *
          (if (XiTail system coarse candidate = source ∧ XiHead system coarse candidate = target) ∨
              (XiTail system coarse candidate = target ∧ XiHead system coarse candidate = source) then
            (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1))
              (XiCol system.toRuleData coarse candidate))⁻¹ else 0))
      (fun candidate _ => mul_nonneg (pow_nonneg ratePositive.le steps) (by
        split
        · exact (inv_pos.mpr (ruleFamily_Psi_iterate_positive system rulesConnected
            (fun _ => 1) (fun _ => by norm_num) steps _)).le
        · exact le_rfl)) (Finset.mem_univ edge)
    simpa only [if_pos endpoints] using bound

end
end EIGS

#print axioms EIGS.Network.unique_endpoint_weight_sum_le
#print axioms EIGS.exists_xiNormalizedSkeletonConductance_edge_bounds
