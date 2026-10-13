import RequestProject.Section31.EIGSHarmonicContraction

/-! Harmonic values on each actual substituted rule copy lie between the
parent edge values. Iterated cell oscillation uses this convexity together with
the separately proved geometric edge decay. -/

namespace EIGS.Network

open IGS.Sec31

variable {K : ℕ} (network : Network K)

theorem unit_potential_minimum_range
    (resistances : Fin K → ℝ) (resistancesPositive : ∀ colour, 0 < resistances colour)
    (connected : network.toSimpleGraph.Connected) (source sink : network.V)
    (potential : network.V → ℝ) (sourceValue : potential source = 1) (sinkValue : potential sink = 0)
    (potentialMinimal : ∀ competitor : network.V → ℝ,
      competitor source = 1 → competitor sink = 0 →
      (network.potentialNetwork resistances resistancesPositive).energy potential ≤
        (network.potentialNetwork resistances resistancesPositive).energy competitor) :
    ∀ vertex, 0 ≤ potential vertex ∧ potential vertex ≤ 1 := by
  classical
  obtain ⟨poincareConstant, poincareNonnegative, poincareBound⟩ :=
    network.exists_potential_poincare_constant resistances resistancesPositive source connected
  apply (network.potentialNetwork resistances resistancesPositive).range_subset_of_min
    {source, sink} potential poincareConstant
    (fun values boundaryZero vertex => poincareBound values (boundaryZero source (by simp)) vertex)
  · intro vertex membership
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using membership :
      vertex = source ∨ vertex = sink) with vertexSource | vertexSink
    · subst vertex; simp [sourceValue]
    · subst vertex; simp [sinkValue]
  · intro _ _; rfl
  · intro competitor competitorBoundary
    apply potentialMinimal competitor
    · simpa [sourceValue] using competitorBoundary source (by simp)
    · simpa [sinkValue] using competitorBoundary sink (by simp)

end EIGS.Network

namespace EIGS

variable {K : ℕ}

private theorem affine_mem_endpoint_interval (first second weight : ℝ)
    (weightNonnegative : 0 ≤ weight) (weightAtMostOne : weight ≤ 1) :
    min first second ≤ second + (first - second) * weight ∧
      second + (first - second) * weight ≤ max first second := by
  by_cases endpointsOrdered : first ≤ second
  · rw [min_eq_left endpointsOrdered, max_eq_right endpointsOrdered]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 endpointsOrdered) (sub_nonneg.2 weightAtMostOne)]
    · nlinarith [mul_nonneg (sub_nonneg.2 endpointsOrdered) weightNonnegative]
  · have reverseOrder : second ≤ first := le_of_not_ge endpointsOrdered
    rw [min_eq_right reverseOrder, max_eq_left reverseOrder]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 reverseOrder) weightNonnegative]
    · nlinarith [mul_nonneg (sub_nonneg.2 reverseOrder) (sub_nonneg.2 weightAtMostOne)]

theorem xiHarmonicStep_rule_vertex_range (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour =
        resistanceRate * resistanceVector colour)
    (level : ℕ) (oldValues : XiVtx system level → ℝ)
    (edge : XiEdge system.toRuleData level)
    (vertex : (system.rule (XiCol system.toRuleData level edge)).V) :
    min (oldValues (XiTail system level edge)) (oldValues (XiHead system level edge)) ≤
        xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair level oldValues
            (embedRuleVtx system level edge (XiTail system level edge) (XiHead system level edge) vertex) ∧
      xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair level oldValues
            (embedRuleVtx system level edge (XiTail system level edge) (XiHead system level edge) vertex) ≤
        max (oldValues (XiTail system level edge)) (oldValues (XiHead system level edge)) := by
  classical
  have profilesExist := fun colour =>
    (system.ruleNetwork colour).exists_minimum_potential_energy_eq_inverse_effRes resistanceVector
      resistanceVectorPositive (rulesConnected colour) (system.plantPlus colour) (system.plantMinus colour)
        (system.plant_ne colour)
  choose profiles profilesPlus profilesMinus profilesMinimal profilesEnergy using profilesExist
  have profileRange := (system.ruleNetwork (XiCol system.toRuleData level edge)).unit_potential_minimum_range
    resistanceVector resistanceVectorPositive (rulesConnected _) _ _ (profiles _)
      (profilesPlus _) (profilesMinus _) (profilesMinimal _) vertex
  rw [xiHarmonicStep_eq_affine_profiles system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair profiles profilesPlus profilesMinus profilesMinimal]
  change min (oldValues (XiTail system level edge)) (oldValues (XiHead system level edge)) ≤
      (XiNetwork system level).substAffineProfiles (system.ruleFamily rulesConnected) profiles oldValues
        ((XiNetwork system level).substEmbed (system.ruleFamily rulesConnected) edge vertex) ∧
    (XiNetwork system level).substAffineProfiles (system.ruleFamily rulesConnected) profiles oldValues
        ((XiNetwork system level).substEmbed (system.ruleFamily rulesConnected) edge vertex) ≤
      max (oldValues (XiTail system level edge)) (oldValues (XiHead system level edge))
  rw [(XiNetwork system level).substAffineProfiles_restrict (system.ruleFamily rulesConnected)
    profiles profilesPlus profilesMinus]
  exact affine_mem_endpoint_interval _ _ _ profileRange.1 profileRange.2

def xiAncestorEdge (system : EIGSData K) (initialLevel : ℕ) :
    (offset : ℕ) → XiEdge system.toRuleData (initialLevel + offset) → XiEdge system.toRuleData initialLevel
  | 0 => id
  | offset + 1 => fun edge => xiAncestorEdge system initialLevel offset edge.1

end EIGS
