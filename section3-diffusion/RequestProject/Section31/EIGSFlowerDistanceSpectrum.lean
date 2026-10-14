import RequestProject.Section31.EIGSFlowerRuleSimplicity
import RequestProject.Section31.EIGSFlowerRuleConnectivity
import RequestProject.Section2ConcreteSpectralRadius

/-! The weighted terminal distance is computed on the actual flower,
using an explicit branch walk and the height Lipschitz potential. -/

namespace EIGS
noncomputable section
open scoped Classical

def flowerBranchPrefix (branches segments : ℕ) (branch : Fin branches) :
    (count : ℕ) → (bound : count ≤ segments) →
      ((flowerSystem branches segments).ruleNetwork 0).EdgeWalk (Sum.inl false)
        (flowerPoint branches segments branch ⟨count, by omega⟩)
  | 0, _ => by
      simpa [flowerPoint] using
        (Network.EdgeWalk.nil (network := (flowerSystem branches segments).ruleNetwork 0) (Sum.inl false))
  | count + 1, bound => by
      let edge : Fin branches × Fin segments := (branch, ⟨count, by omega⟩)
      apply (flowerBranchPrefix branches segments branch count (by omega)).append
      refine Network.EdgeWalk.cons edge ?_ (.nil _)
      by_cases backwards : branch.val = 0
      · right
        simp [edge, EIGSData.ruleNetwork, flowerSystem, flowerGraph,
          flowerEdgeStart, flowerEdgeEnd, backwards]
      · left
        simp [edge, EIGSData.ruleNetwork, flowerSystem, flowerGraph,
          flowerEdgeStart, flowerEdgeEnd, backwards]

theorem flowerBranchPrefix_cost (branches segments : ℕ) (branch : Fin branches)
    (lengths : Fin 1 → ℝ) (count : ℕ) (bound : count ≤ segments) :
    (flowerBranchPrefix branches segments branch count bound).cost lengths =
      (count : ℝ) * lengths 0 := by
  induction count with
  | zero => simp [flowerBranchPrefix, Network.EdgeWalk.cost]
  | succ count induction =>
      simp [flowerBranchPrefix, Network.EdgeWalk.cost_append, Network.EdgeWalk.cost,
        induction, EIGSData.ruleNetwork, flowerSystem, flowerGraph, Nat.cast_add, Nat.cast_one]
      <;> ring

theorem flowerHeightMetricPotential_lipschitz (branches segments : ℕ)
    (lengths : Fin 1 → ℝ) (nonnegative : 0 ≤ lengths) :
    ((flowerSystem branches segments).ruleNetwork 0).EdgeLipschitz lengths
      (fun vertex => lengths 0 * (flowerHeight branches segments vertex : ℝ)) := by
  intro edge
  change |lengths 0 * (flowerHeight branches segments ((flowerGraph branches segments).tail edge) : ℝ) -
    lengths 0 * (flowerHeight branches segments ((flowerGraph branches segments).head edge) : ℝ)| ≤ lengths 0
  rcases flowerGraph_edge_height branches segments edge with heights | heights <;>
    rw [heights.1, heights.2] <;> push_cast <;>
    ring_nf <;> simp [abs_neg, abs_of_nonneg (nonnegative 0)]

theorem flowerSystem_metricLengths (branches segments : ℕ)
    (branchesPositive : 0 < branches) (segmentsAtLeastTwo : 2 ≤ segments)
    (lengths : Fin 1 → ℝ) (nonnegative : 0 ≤ lengths) :
    ((flowerSystem branches segments).ruleFamily
      (flowerSystem_connected branches segments branchesPositive segmentsAtLeastTwo)).metricLengths lengths =
        fun _ => (segments : ℝ) * lengths 0 := by
  funext colour
  have colourZero : colour = 0 := Subsingleton.elim _ _
  subst colour
  change ((flowerSystem branches segments).ruleNetwork 0).weightedDistance lengths
    (Sum.inl false) (Sum.inl true) = (segments : ℝ) * lengths 0
  apply le_antisymm
  · let branch : Fin branches := ⟨0, branchesPositive⟩
    let terminalWalk := (flowerBranchPrefix branches segments branch segments le_rfl).copy rfl
      (show flowerPoint branches segments branch ⟨segments, by omega⟩ = Sum.inl true by
        simp [flowerPoint, show segments ≠ 0 by omega])
    have bound := ((flowerSystem branches segments).ruleNetwork 0).weightedDistance_le_cost
      nonnegative terminalWalk
    simpa only [terminalWalk, Network.EdgeWalk.cost_copy, flowerBranchPrefix_cost] using bound
  · have bound := ((flowerSystem branches segments).ruleNetwork 0).potential_difference_le_weightedDistance
      (flowerSystem_connected branches segments branchesPositive segmentsAtLeastTwo 0)
      (flowerHeightMetricPotential_lipschitz branches segments lengths nonnegative)
      (Sum.inl false) (Sum.inl true)
    simpa [flowerHeight, abs_mul, abs_of_nonneg (nonnegative 0),
      abs_of_nonneg (Nat.cast_nonneg segments : (0 : ℝ) ≤ segments), mul_comm] using bound

end
end EIGS

#print axioms EIGS.flowerBranchPrefix_cost
#print axioms EIGS.flowerHeightMetricPotential_lipschitz
#print axioms EIGS.flowerSystem_metricLengths
