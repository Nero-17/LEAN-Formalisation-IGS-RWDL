import RequestProject.Section31.EIGSUVFlowerRuleConnectivity
import RequestProject.Section31.EIGSUVFlowerRuleSimplicity
import RequestProject.Section31.EIGSUVFlowerFraction
import RequestProject.Section2ConcreteSpectralRadius

/-! Weighted terminal distance of the actual unequal-path flower.
Both explicit path walks give the upper bound. The common normalized
path position, scaled by min(u,v), gives the matching Lipschitz bound. -/

namespace EIGS
noncomputable section
open scoped Classical

def uvFlowerLeftPrefix (firstLength secondLength : ℕ) :
    (count : ℕ) → (bound : count ≤ firstLength) →
      ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).EdgeWalk (Sum.inl false)
        (uvFlowerLeftEmbedding firstLength secondLength
          (uvFlowerPathPoint firstLength ⟨count, by omega⟩))
  | 0, _ => by
    simpa [uvFlowerPathPoint, uvFlowerLeftEmbedding] using
      (Network.EdgeWalk.nil (network := (uvFlowerSystem firstLength secondLength).ruleNetwork 0) (Sum.inl false))
  | count + 1, bound => by
    let edge : Fin firstLength := ⟨count, by omega⟩
    apply (uvFlowerLeftPrefix firstLength secondLength count (by omega)).append
    refine Network.EdgeWalk.cons (Sum.inl edge) ?_ (.nil _)
    right
    simp [edge, EIGSData.ruleNetwork, uvFlowerSystem, uvFlowerRuleGraph,
      uvFlowerPathHead_eq_point, uvFlowerPathTail_eq_point]

def uvFlowerRightPrefix (firstLength secondLength : ℕ) :
    (count : ℕ) → (bound : count ≤ secondLength) →
      ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).EdgeWalk (Sum.inl false)
        (uvFlowerRightEmbedding firstLength secondLength
          (uvFlowerPathPoint secondLength ⟨count, by omega⟩))
  | 0, _ => by
    simpa [uvFlowerPathPoint, uvFlowerRightEmbedding] using
      (Network.EdgeWalk.nil (network := (uvFlowerSystem firstLength secondLength).ruleNetwork 0) (Sum.inl false))
  | count + 1, bound => by
    let edge : Fin secondLength := ⟨count, by omega⟩
    apply (uvFlowerRightPrefix firstLength secondLength count (by omega)).append
    refine Network.EdgeWalk.cons (Sum.inr edge) ?_ (.nil _)
    left
    simp [edge, EIGSData.ruleNetwork, uvFlowerSystem, uvFlowerRuleGraph,
      uvFlowerPathHead_eq_point, uvFlowerPathTail_eq_point]

theorem uvFlowerLeftPrefix_cost (firstLength secondLength : ℕ) (lengths : Fin 1 → ℝ)
    (count : ℕ) (bound : count ≤ firstLength) :
    (uvFlowerLeftPrefix firstLength secondLength count bound).cost lengths = (count : ℝ) * lengths 0 := by
  induction count with
  | zero => simp [uvFlowerLeftPrefix, Network.EdgeWalk.cost]
  | succ count induction =>
    simp [uvFlowerLeftPrefix, Network.EdgeWalk.cost_append, Network.EdgeWalk.cost,
      induction, EIGSData.ruleNetwork, uvFlowerSystem, uvFlowerRuleGraph, Nat.cast_add, Nat.cast_one]
    <;> ring

theorem uvFlowerRightPrefix_cost (firstLength secondLength : ℕ) (lengths : Fin 1 → ℝ)
    (count : ℕ) (bound : count ≤ secondLength) :
    (uvFlowerRightPrefix firstLength secondLength count bound).cost lengths = (count : ℝ) * lengths 0 := by
  induction count with
  | zero => simp [uvFlowerRightPrefix, Network.EdgeWalk.cost]
  | succ count induction =>
    simp [uvFlowerRightPrefix, Network.EdgeWalk.cost_append, Network.EdgeWalk.cost,
      induction, EIGSData.ruleNetwork, uvFlowerSystem, uvFlowerRuleGraph, Nat.cast_add, Nat.cast_one]
    <;> ring

theorem uvFlowerMetricPotential_lipschitz (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength)
    (lengths : Fin 1 → ℝ) (nonnegative : 0 ≤ lengths) :
    ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).EdgeLipschitz lengths
      (fun vertex => lengths 0 * (min firstLength secondLength : ℕ) *
        uvFlowerFraction firstLength secondLength vertex) := by
  intro edge
  change |lengths 0 * (min firstLength secondLength : ℕ) *
        uvFlowerFraction firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).tail edge) -
      lengths 0 * (min firstLength secondLength : ℕ) *
        uvFlowerFraction firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).head edge)| ≤ lengths 0
  rw [show lengths 0 * (min firstLength secondLength : ℕ) *
        uvFlowerFraction firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).tail edge) -
      lengths 0 * (min firstLength secondLength : ℕ) *
        uvFlowerFraction firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).head edge) =
      (lengths 0 * (min firstLength secondLength : ℕ)) *
        (uvFlowerFraction firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).tail edge) -
          uvFlowerFraction firstLength secondLength ((uvFlowerRuleGraph firstLength secondLength).head edge)) by ring,
    uvFlowerFraction_edge firstLength secondLength firstPositive secondPositive]
  have coefficientNonnegative : 0 ≤ lengths 0 * (min firstLength secondLength : ℕ) :=
    mul_nonneg (nonnegative 0) (Nat.cast_nonneg _)
  cases edge with
  | inl edge =>
    have firstCastPositive : (0 : ℝ) < firstLength := Nat.cast_pos.mpr firstPositive
    simp only [Sum.elim_inl, mul_one_div]
    rw [abs_of_nonneg (div_nonneg coefficientNonnegative firstCastPositive.le)]
    apply (div_le_iff₀ firstCastPositive).2
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.min_le_left firstLength secondLength)) (nonnegative 0)
  | inr edge =>
    have secondCastPositive : (0 : ℝ) < secondLength := Nat.cast_pos.mpr secondPositive
    simp only [Sum.elim_inr, mul_neg, mul_one_div, abs_neg]
    rw [abs_of_nonneg (div_nonneg coefficientNonnegative secondCastPositive.le)]
    apply (div_le_iff₀ secondCastPositive).2
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.min_le_right firstLength secondLength)) (nonnegative 0)

theorem uvFlowerSystem_metricLengths (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength)
    (lengths : Fin 1 → ℝ) (nonnegative : 0 ≤ lengths) :
    ((uvFlowerSystem firstLength secondLength).ruleFamily
      (uvFlowerSystem_connected firstLength secondLength firstPositive secondPositive)).metricLengths lengths =
      fun _ => (min firstLength secondLength : ℕ) * lengths 0 := by
  funext colour
  have colourZero : colour = 0 := Subsingleton.elim _ _
  subst colour
  change ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).weightedDistance lengths
    (Sum.inl false) (Sum.inl true) = (min firstLength secondLength : ℕ) * lengths 0
  apply le_antisymm
  · let leftWalk := (uvFlowerLeftPrefix firstLength secondLength firstLength le_rfl).copy rfl
      (show uvFlowerLeftEmbedding firstLength secondLength
          (uvFlowerPathPoint firstLength ⟨firstLength, by omega⟩) = Sum.inl true by
        simp [uvFlowerPathPoint, uvFlowerLeftEmbedding, Nat.ne_of_gt firstPositive])
    let rightWalk := (uvFlowerRightPrefix firstLength secondLength secondLength le_rfl).copy rfl
      (show uvFlowerRightEmbedding firstLength secondLength
          (uvFlowerPathPoint secondLength ⟨secondLength, by omega⟩) = Sum.inl true by
        simp [uvFlowerPathPoint, uvFlowerRightEmbedding, Nat.ne_of_gt secondPositive])
    have leftBound := ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).weightedDistance_le_cost
      nonnegative leftWalk
    have rightBound := ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).weightedDistance_le_cost
      nonnegative rightWalk
    simp only [leftWalk, Network.EdgeWalk.cost_copy, uvFlowerLeftPrefix_cost] at leftBound
    simp only [rightWalk, Network.EdgeWalk.cost_copy, uvFlowerRightPrefix_cost] at rightBound
    rw [Nat.cast_min, min_mul_of_nonneg _ _ (nonnegative 0)]
    exact le_min leftBound rightBound
  · have bound := ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).potential_difference_le_weightedDistance
      (uvFlowerSystem_connected firstLength secondLength firstPositive secondPositive 0)
      (uvFlowerMetricPotential_lipschitz firstLength secondLength firstPositive secondPositive lengths nonnegative)
      (Sum.inl false) (Sum.inl true)
    change |lengths 0 * (min firstLength secondLength : ℕ) * 0 -
        lengths 0 * (min firstLength secondLength : ℕ) * 1| ≤
      ((uvFlowerSystem firstLength secondLength).ruleNetwork 0).weightedDistance lengths
        (Sum.inl false) (Sum.inl true) at bound
    rw [mul_zero, mul_one, zero_sub, abs_neg,
      abs_of_nonneg (mul_nonneg (nonnegative 0) (Nat.cast_nonneg (min firstLength secondLength)))] at bound
    simpa only [mul_comm] using bound

theorem uvFlowerSystem_distanceSpectralRadius (firstLength secondLength : ℕ)
    (firstAtLeastTwo : 2 ≤ firstLength) (secondAtLeastTwo : 2 ≤ secondLength) :
    (uvFlowerSystem firstLength secondLength).distanceSpectralRadius
      (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega)) =
        (min firstLength secondLength : ℕ) := by
  obtain ⟨lengths, positive, ratePositive, normalized, eigenpair⟩ :=
    (uvFlowerSystem firstLength secondLength).metricLengths_spectral_eigenpair
      (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega))
      (uvFlowerSystem_loopless firstLength secondLength)
      (uvFlowerSystem_edgesUnique firstLength secondLength firstAtLeastTwo secondAtLeastTwo)
      (uvFlowerSystem_distancePositive firstLength secondLength)
  rw [uvFlowerSystem_metricLengths firstLength secondLength (by omega) (by omega)
    lengths (fun colour => (positive colour).le)] at eigenpair
  have coordinate := congrFun eigenpair 0
  simp only [Pi.smul_apply, smul_eq_mul] at coordinate
  have lengthPositive := positive 0
  nlinarith

end
end EIGS

#print axioms EIGS.uvFlowerLeftPrefix_cost
#print axioms EIGS.uvFlowerRightPrefix_cost
#print axioms EIGS.uvFlowerMetricPotential_lipschitz
#print axioms EIGS.uvFlowerSystem_metricLengths
#print axioms EIGS.uvFlowerSystem_distanceSpectralRadius
