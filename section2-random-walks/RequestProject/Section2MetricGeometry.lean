import RequestProject.Section2ConcreteMetric
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Data.Finset.Lattice.Fold

/-! Positive weighted distances and the compatible metric on actual Xi levels.
The colour lengths will be supplied by the already proved positive path
eigenvector. No interlevel metric compatibility is assumed. -/

namespace EIGS.Network

variable {K : ℕ} (network : Network K)

theorem EdgeWalk.cost_smul (lengths : Fin K → ℝ) (scale : ℝ)
    {source sink : network.V} (walk : network.EdgeWalk source sink) :
    walk.cost (scale • lengths) = scale * walk.cost lengths := by
  induction walk with
  | nil => simp [EdgeWalk.cost]
  | cons edge joins rest induction_hypothesis =>
    simp [EdgeWalk.cost, induction_hypothesis, mul_add]

theorem weightedDistance_smul (lengths : Fin K → ℝ) {scale : ℝ}
    (scaleNonnegative : 0 ≤ scale) (source sink : network.V) :
    network.weightedDistance (scale • lengths) source sink =
      scale * network.weightedDistance lengths source sink := by
  unfold weightedDistance
  simp_rw [EdgeWalk.cost_smul]
  exact (Real.mul_iInf_of_nonneg scaleNonnegative _).symm

theorem weightedDistance_lower_bound
    (connected : network.toSimpleGraph.Connected) {lengths : Fin K → ℝ}
    {lower : ℝ} (lowerNonnegative : 0 ≤ lower)
    (lowerBound : ∀ colour, lower ≤ lengths colour)
    (source sink : network.V) (distinct : source ≠ sink) :
    lower ≤ network.weightedDistance lengths source sink := by
  classical
  have lipschitz : network.EdgeLipschitz lengths
      (fun vertex => if vertex = source then lower else 0) := by
    intro edge
    dsimp only
    split_ifs <;> simp only [sub_self, abs_zero, sub_zero, zero_sub, abs_neg,
      abs_of_nonneg lowerNonnegative] <;>
      first | exact lowerBound _ | exact lowerNonnegative.trans (lowerBound _)
  have bound := network.potential_difference_le_weightedDistance connected lipschitz source sink
  simpa [distinct, Ne.symm distinct, abs_of_nonneg lowerNonnegative] using bound

theorem weightedDistance_pos [Nonempty (Fin K)]
    (connected : network.toSimpleGraph.Connected) {lengths : Fin K → ℝ}
    (lengthsPositive : ∀ colour, 0 < lengths colour)
    (source sink : network.V) (distinct : source ≠ sink) :
    0 < network.weightedDistance lengths source sink := by
  classical
  have positiveMinimum : 0 < Finset.univ.inf' Finset.univ_nonempty lengths :=
    (Finset.lt_inf'_iff _).mpr (fun colour _ => lengthsPositive colour)
  exact positiveMinimum.trans_le (network.weightedDistance_lower_bound connected
    positiveMinimum.le (fun colour => Finset.inf'_le lengths (Finset.mem_univ colour))
    source sink distinct)

/-- The metric structure uses the actual labelled walk infimum. -/
noncomputable def weightedMetricSpace [Nonempty (Fin K)]
    (connected : network.toSimpleGraph.Connected) (lengths : Fin K → ℝ)
    (lengthsPositive : ∀ colour, 0 < lengths colour) : MetricSpace network.V where
  dist := network.weightedDistance lengths
  dist_self := network.weightedDistance_self (fun colour => (lengthsPositive colour).le)
  dist_comm := network.weightedDistance_symm connected (fun colour => (lengthsPositive colour).le)
  dist_triangle := network.weightedDistance_triangle connected (fun colour => (lengthsPositive colour).le)
  eq_of_dist_eq_zero := by
    intro source sink distanceZero
    by_contra distinct
    exact (ne_of_gt (network.weightedDistance_pos connected lengthsPositive source sink distinct)) distanceZero

end EIGS.Network

namespace EIGS

variable {K : ℕ}

noncomputable def xiScaledWeightedDistance (system : EIGSData K) (lengths : Fin K → ℝ)
    (rate : ℝ) (level : ℕ) (source sink : XiVtx system level) : ℝ :=
  rate⁻¹ ^ level * (XiNetwork system level).weightedDistance lengths source sink

theorem xiScaledWeightedDistance_old (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    {lengths : Fin K → ℝ} (lengthsNonnegative : 0 ≤ lengths)
    {rate : ℝ} (ratePositive : 0 < rate)
    (eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths = rate • lengths)
    (level : ℕ) (source sink : XiVtx system level) :
    xiScaledWeightedDistance system lengths rate (level + 1) (Sum.inl source) (Sum.inl sink) =
      xiScaledWeightedDistance system lengths rate level source sink := by
  unfold xiScaledWeightedDistance
  rw [xiNetwork_weightedDistance_succ system ruleConnected lengthsNonnegative,
    eigenpair, Network.weightedDistance_smul _ _ ratePositive.le, pow_succ]
  field_simp

end EIGS

#print axioms EIGS.Network.weightedDistance_smul
#print axioms EIGS.Network.weightedDistance_pos
#print axioms EIGS.Network.weightedMetricSpace
#print axioms EIGS.xiScaledWeightedDistance_old
