import RequestProject.Section2MetricGeometry

/-! Uniform comparison of original unit graph distances and actual positive
colour-weighted distances. This applies at every Xi level and every pair. -/

namespace EIGS.Network

variable {K : ℕ} (network : Network K)

theorem EdgeWalk.cost_mono {first second : Fin K → ℝ} (lengths_le : first ≤ second)
    {source sink : network.V} (walk : network.EdgeWalk source sink) :
    walk.cost first ≤ walk.cost second := by
  induction walk with
  | nil => exact le_rfl
  | cons edge joins rest induction_hypothesis =>
    exact add_le_add (lengths_le (network.color edge)) induction_hypothesis

theorem weightedDistance_mono (connected : network.toSimpleGraph.Connected)
    {first second : Fin K → ℝ} (first_nonnegative : 0 ≤ first) (lengths_le : first ≤ second)
    (source sink : network.V) :
    network.weightedDistance first source sink ≤ network.weightedDistance second source sink := by
  letI := network.edgeWalk_nonempty_of_connected connected source sink
  apply le_ciInf
  intro walk
  exact (network.weightedDistance_le_cost first_nonnegative walk).trans
    (walk.cost_mono network lengths_le)

theorem weightedDistance_length_bounds (connected : network.toSimpleGraph.Connected)
    (loopless : network.Loopless) {lengths : Fin K → ℝ} {lower upper : ℝ}
    (lower_nonnegative : 0 ≤ lower) (upper_nonnegative : 0 ≤ upper)
    (lower_bound : ∀ colour, lower ≤ lengths colour)
    (upper_bound : ∀ colour, lengths colour ≤ upper) (source sink : network.V) :
    lower * (network.toSimpleGraph.dist source sink : ℝ) ≤
      network.weightedDistance lengths source sink ∧
    network.weightedDistance lengths source sink ≤
      upper * (network.toSimpleGraph.dist source sink : ℝ) := by
  have unit_metric := network.weightedDistance_unit_eq_graphDistance connected loopless source sink
  constructor
  · rw [← unit_metric, ← network.weightedDistance_smul (fun _ : Fin K => (1 : ℝ)) lower_nonnegative]
    exact network.weightedDistance_mono connected (first := lower • (fun _ : Fin K => (1 : ℝ)))
      (fun colour => by simpa only [Pi.smul_apply, smul_eq_mul, mul_one] using lower_nonnegative)
      (fun colour => by simpa only [Pi.smul_apply, smul_eq_mul, mul_one] using lower_bound colour)
      source sink
  · rw [← unit_metric, ← network.weightedDistance_smul (fun _ : Fin K => (1 : ℝ)) upper_nonnegative]
    exact network.weightedDistance_mono connected
      (fun colour => lower_nonnegative.trans (lower_bound colour))
      (fun colour => by simpa only [Pi.smul_apply, smul_eq_mul, mul_one] using upper_bound colour)
      source sink

end EIGS.Network

namespace EIGS

variable {K : ℕ}

theorem xiScaled_unit_distance_comparable (system : EIGSData K)
    (rule_connected : ∀ colour, (ruleSG system colour).Connected)
    (rules_loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    {lengths : Fin K → ℝ} (lengths_positive : ∀ colour, 0 < lengths colour)
    {rate : ℝ} (rate_positive : 0 < rate) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ level (source sink : XiVtx system level),
        lower * ((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level ≤
          xiScaledWeightedDistance system lengths rate level source sink ∧
        xiScaledWeightedDistance system lengths rate level source sink ≤
          upper * ((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level := by
  classical
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  let lower := Finset.univ.inf' Finset.univ_nonempty lengths
  let upper := Finset.univ.sup' Finset.univ_nonempty lengths
  have lower_positive : 0 < lower :=
    (Finset.lt_inf'_iff _).mpr (fun colour _ => lengths_positive colour)
  have upper_positive : 0 < upper :=
    (lengths_positive system.initCol).trans_le (Finset.le_sup' lengths (Finset.mem_univ _))
  refine ⟨lower, upper, lower_positive, upper_positive, fun level source sink => ?_⟩
  have bounds := (XiNetwork system level).weightedDistance_length_bounds
    (xiSimpleGraph_connected system rule_connected level)
    (xiNetwork_loopless system rule_connected rules_loopless level)
    lower_positive.le upper_positive.le
    (fun colour => Finset.inf'_le lengths (Finset.mem_univ colour))
    (fun colour => Finset.le_sup' lengths (Finset.mem_univ colour)) source sink
  constructor
  · have scaled := mul_le_mul_of_nonneg_left bounds.1
      (pow_nonneg (inv_nonneg.mpr rate_positive.le) level)
    simpa only [xiScaledWeightedDistance, inv_pow, div_eq_mul_inv, mul_comm, mul_left_comm] using scaled
  · have scaled := mul_le_mul_of_nonneg_left bounds.2
      (pow_nonneg (inv_nonneg.mpr rate_positive.le) level)
    simpa only [xiScaledWeightedDistance, inv_pow, div_eq_mul_inv, mul_comm, mul_left_comm] using scaled

end EIGS

#print axioms EIGS.Network.weightedDistance_mono
#print axioms EIGS.xiScaled_unit_distance_comparable
