import RequestProject.Section31.EIGSFiniteHausdorff
import RequestProject.Section2UnitMetricLimit
import RequestProject.Section2MetricComparison

/-! Uniform, over all vertices of the growing graphs, convergence of original
unit distances to the compatible weighted metric. Finite coarse convergence
is upgraded using actual parent nets and the level-uniform metric comparison. -/

namespace EIGS

open Filter Topology Metric
open scoped BigOperators

variable {K : ℕ}

theorem xiLiftVertices_eq_xiForward (system : EIGSData K) (coarse steps : ℕ)
    (vertex : XiVtx system coarse) :
    xiLiftVertices system coarse steps vertex = xiForward system coarse steps vertex := by
  induction steps with
  | zero => rfl
  | succ steps induction_hypothesis =>
    simpa only [xiLiftVertices, xiForward] using congrArg Sum.inl induction_hypothesis

theorem xiUnitLevel_dist_eq (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rate : ℝ) (ratePositive : 0 < rate) (level : ℕ) (source sink : XiVtx system level) :
    letI := xiLevelMetricSpace system connected (fun _ => 1) (fun _ => zero_lt_one) rate ratePositive level
    dist source sink = ((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level := by
  change rate⁻¹ ^ level * (XiNetwork system level).weightedDistance (fun _ => 1) source sink = _
  rw [Network.weightedDistance_unit_eq_graphDistance (XiNetwork system level)
    (xiSimpleGraph_connected system connected level) (xiNetwork_loopless system connected loopless level)]
  simp only [inv_pow, div_eq_mul_inv, mul_comm]
  rfl

private theorem uniform_metric_limit_of_coarse (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (scale : ℝ) (scalePositive : 0 < scale)
    (coarseConvergence : ∀ coarse (source sink : XiVtx system coarse),
      Tendsto (fun steps => ((XiSimpleGraph system (coarse + steps)).dist
        (xiForward system coarse steps source) (xiForward system coarse steps sink) : ℝ) /
          rate ^ (coarse + steps)) atTop
        (nhds (scale * xiScaledWeightedDistance system lengths rate coarse source sink))) :
    ∀ tolerance : ℝ, 0 < tolerance → ∃ threshold : ℕ, ∀ level, threshold ≤ level →
      ∀ source sink : XiVtx system level,
        |((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level -
          scale * xiScaledWeightedDistance system lengths rate level source sink| < tolerance := by
  have ratePositive : 0 < rate := zero_lt_one.trans rateGreaterThanOne
  obtain ⟨lower, upper, lowerPositive, upperPositive, comparison⟩ :=
    xiScaled_unit_distance_comparable system connected loopless lengthsPositive ratePositive
  intro tolerance tolerancePositive
  have radiusConvergence :=
    (xiFiniteNetRadius_tendsto_zero system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair).const_mul
      (2 / lower + 2 * scale)
  simp only [mul_zero] at radiusConvergence
  have eventuallySmall := radiusConvergence.eventually (gt_mem_nhds (half_pos tolerancePositive))
  obtain ⟨coarse, coarseSmall⟩ := eventuallySmall.exists
  have coarseSmall' : (2 / lower + 2 * scale) *
      (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (coarse + 1)) < tolerance / 2 := by
    simpa only [mul_zero] using coarseSmall
  have eventuallyPairs : ∀ᶠ steps in atTop, ∀ first second : XiVtx system coarse,
      |((XiSimpleGraph system (coarse + steps)).dist
        (xiForward system coarse steps first) (xiForward system coarse steps second) : ℝ) /
          rate ^ (coarse + steps) -
          scale * xiScaledWeightedDistance system lengths rate coarse first second| < tolerance / 2 := by
    rw [eventually_all]
    intro first
    rw [eventually_all]
    intro second
    simpa only [Metric.mem_ball, Real.dist_eq] using
      (coarseConvergence coarse first second).eventually (Metric.ball_mem_nhds _ (half_pos tolerancePositive))
  obtain ⟨offsetThreshold, offsetBound⟩ := eventually_atTop.mp eventuallyPairs
  refine ⟨coarse + offsetThreshold, ?_⟩
  intro level levelBound
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.le_add_right coarse offsetThreshold).trans levelBound)
  have stepsBound : offsetThreshold ≤ steps := by omega
  intro source sink
  obtain ⟨first, firstBound⟩ := xiUnion_finite_net system connected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair coarse (xiVertexEmbedding system (coarse + steps) source)
  obtain ⟨second, secondBound⟩ := xiUnion_finite_net system connected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair coarse (xiVertexEmbedding system (coarse + steps) sink)
  rw [← xiVertexEmbedding_lift system coarse steps first,
    xiUnionDistance_embedding system connected lengths lengthsPositive rate ratePositive eigenpair,
    xiLiftVertices_eq_xiForward] at firstBound
  rw [← xiVertexEmbedding_lift system coarse steps second,
    xiUnionDistance_embedding system connected lengths lengthsPositive rate ratePositive eigenpair,
    xiLiftVertices_eq_xiForward] at secondBound
  have firstUnitBound :
      ((XiSimpleGraph system (coarse + steps)).dist source (xiForward system coarse steps first) : ℝ) /
        rate ^ (coarse + steps) ≤
        (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (coarse + 1)) / lower := by
    apply (le_div_iff₀ lowerPositive).mpr
    have lowerBound := (comparison (coarse + steps) source (xiForward system coarse steps first)).1
    rw [mul_div_assoc] at lowerBound
    nlinarith only [lowerBound, firstBound]
  have secondUnitBound :
      ((XiSimpleGraph system (coarse + steps)).dist sink (xiForward system coarse steps second) : ℝ) /
        rate ^ (coarse + steps) ≤
        (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (coarse + 1)) / lower := by
    apply (le_div_iff₀ lowerPositive).mpr
    have lowerBound := (comparison (coarse + steps) sink (xiForward system coarse steps second)).1
    rw [mul_div_assoc] at lowerBound
    nlinarith only [lowerBound, secondBound]
  have unitChange :
      |((XiSimpleGraph system (coarse + steps)).dist source sink : ℝ) / rate ^ (coarse + steps) -
        ((XiSimpleGraph system (coarse + steps)).dist (xiForward system coarse steps first)
          (xiForward system coarse steps second) : ℝ) / rate ^ (coarse + steps)| ≤
        2 * (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (coarse + 1)) / lower := by
    letI := xiLevelMetricSpace system connected (fun _ => 1) (fun _ => zero_lt_one) rate ratePositive (coarse + steps)
    have distanceChange := dist_dist_dist_le source sink
      (xiForward system coarse steps first) (xiForward system coarse steps second)
    simp only [Real.dist_eq, xiUnitLevel_dist_eq system connected loopless rate ratePositive] at distanceChange
    calc
      _ ≤ _ := distanceChange.trans (add_le_add firstUnitBound secondUnitBound)
      _ = _ := by ring
  have weightedChange :
      |xiScaledWeightedDistance system lengths rate (coarse + steps) source sink -
        xiScaledWeightedDistance system lengths rate coarse first second| ≤
        2 * (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (coarse + 1)) := by
    letI := xiLevelMetricSpace system connected lengths lengthsPositive rate ratePositive (coarse + steps)
    have distanceChange := dist_dist_dist_le source sink
      (xiLiftVertices system coarse steps first) (xiLiftVertices system coarse steps second)
    change |xiScaledWeightedDistance system lengths rate (coarse + steps) source sink -
        xiScaledWeightedDistance system lengths rate (coarse + steps)
          (xiLiftVertices system coarse steps first) (xiLiftVertices system coarse steps second)| ≤
        xiScaledWeightedDistance system lengths rate (coarse + steps) source
          (xiLiftVertices system coarse steps first) +
        xiScaledWeightedDistance system lengths rate (coarse + steps) sink
          (xiLiftVertices system coarse steps second) at distanceChange
    rw [xiScaledWeightedDistance_lift system connected lengths lengthsPositive rate ratePositive eigenpair,
      xiLiftVertices_eq_xiForward, xiLiftVertices_eq_xiForward] at distanceChange
    linarith only [distanceChange, firstBound, secondBound]
  have coarseError := offsetBound steps stepsBound first second
  have firstTriangle := abs_sub_le
    (((XiSimpleGraph system (coarse + steps)).dist source sink : ℝ) / rate ^ (coarse + steps))
    (((XiSimpleGraph system (coarse + steps)).dist (xiForward system coarse steps first)
      (xiForward system coarse steps second) : ℝ) / rate ^ (coarse + steps))
    (scale * xiScaledWeightedDistance system lengths rate (coarse + steps) source sink)
  have secondTriangle := abs_sub_le
    (((XiSimpleGraph system (coarse + steps)).dist (xiForward system coarse steps first)
      (xiForward system coarse steps second) : ℝ) / rate ^ (coarse + steps))
    (scale * xiScaledWeightedDistance system lengths rate coarse first second)
    (scale * xiScaledWeightedDistance system lengths rate (coarse + steps) source sink)
  rw [← mul_sub, abs_mul, abs_of_pos scalePositive] at secondTriangle
  rw [abs_sub_comm (xiScaledWeightedDistance system lengths rate coarse first second)] at secondTriangle
  have weightedScaled := mul_le_mul_of_nonneg_left weightedChange scalePositive.le
  have boundIdentity :
      2 * (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (coarse + 1)) / lower +
        scale * (2 * (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (coarse + 1))) =
      (2 / lower + 2 * scale) * (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (coarse + 1)) := by ring
  linarith only [firstTriangle, secondTriangle, unitChange, coarseError,
    weightedScaled, coarseSmall', boundIdentity]

theorem xiSimpleGraph_uniform_metric_limit (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate) (normalized : (∑ colour, lengths colour) = 1)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths) :
    ∃ scale : ℝ, 0 < scale ∧ ∀ tolerance : ℝ, 0 < tolerance →
      ∃ threshold : ℕ, ∀ level, threshold ≤ level → ∀ source sink : XiVtx system level,
        |((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level -
          scale * xiScaledWeightedDistance system lengths rate level source sink| < tolerance := by
  obtain ⟨scale, scalePositive, coarseConvergence⟩ := xiSimpleGraph_all_coarse_pairs_metric_limit system
    connected loopless unique plantingNonadjacent distancePositive lengthsPositive
    (zero_lt_one.trans rateGreaterThanOne) normalized eigenpair
  exact ⟨scale, scalePositive, uniform_metric_limit_of_coarse system connected loopless lengths
    lengthsPositive rate rateGreaterThanOne eigenpair scale scalePositive coarseConvergence⟩

end EIGS

#print axioms EIGS.xiSimpleGraph_uniform_metric_limit
