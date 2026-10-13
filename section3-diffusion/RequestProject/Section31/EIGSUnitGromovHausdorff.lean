import RequestProject.Section31.EIGSUnitMetricUniform

/-! The original unweighted Xi graphs, normalized by their actual distance
growth and the common Perron scale, converge in Gromov--Hausdorff space. -/

namespace EIGS

open Filter Topology Metric Set GromovHausdorff
open scoped BigOperators

variable {K : ℕ}

noncomputable def xiUnitGHPoint (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (rate : ℝ) (ratePositive : 0 < rate) (scale : ℝ) (scalePositive : 0 < scale) (level : ℕ) : GHSpace :=
  letI := xiLevelMetricSpace system connected (fun _ => scale⁻¹)
    (fun _ => inv_pos.mpr scalePositive) rate ratePositive level
  letI : Nonempty (XiVtx system level) :=
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  toGHSpace (XiVtx system level)

noncomputable def xiWeightedLimitGHPoint (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths) : GHSpace :=
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  letI : Nonempty (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    ⟨xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true⟩
  toGHSpace (XiMetricCompletion system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair)

theorem xiNormalizedUnitLevel_dist_eq (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rate : ℝ) (ratePositive : 0 < rate) (scale : ℝ) (scalePositive : 0 < scale)
    (level : ℕ) (source sink : XiVtx system level) :
    letI := xiLevelMetricSpace system connected (fun _ => scale⁻¹)
      (fun _ => inv_pos.mpr scalePositive) rate ratePositive level
    dist source sink = (((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level) / scale := by
  change rate⁻¹ ^ level * (XiNetwork system level).weightedDistance (fun _ => scale⁻¹) source sink = _
  have lengthsEquality : (fun _ : Fin K => scale⁻¹) = scale⁻¹ • (fun _ : Fin K => (1 : ℝ)) := by
    ext colour
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  rw [lengthsEquality, Network.weightedDistance_smul _ _ (inv_nonneg.mpr scalePositive.le),
    Network.weightedDistance_unit_eq_graphDistance (XiNetwork system level)
      (xiSimpleGraph_connected system connected level) (xiNetwork_loopless system connected loopless level)]
  simp only [div_eq_mul_inv, inv_pow]
  ring_nf
  rfl

private theorem xiUnitGHPoint_dist_le (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (scale : ℝ) (scalePositive : 0 < scale) (level : ℕ) (tolerance : ℝ)
    (distortion : ∀ source sink : XiVtx system level,
      |(((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level) / scale -
        xiScaledWeightedDistance system lengths rate level source sink| ≤ tolerance) :
    dist (xiUnitGHPoint system connected rate (zero_lt_one.trans rateGreaterThanOne) scale scalePositive level)
      (xiWeightedLimitGHPoint system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) ≤
      tolerance / 2 + xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1) := by
  letI := xiLevelMetricSpace system connected (fun _ => scale⁻¹)
    (fun _ => inv_pos.mpr scalePositive) rate (zero_lt_one.trans rateGreaterThanOne) level
  letI : Nonempty (XiVtx system level) :=
    ⟨by simpa only [Nat.zero_add] using xiLiftVertices system 0 level true⟩
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  letI : Nonempty (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
    ⟨xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true⟩
  change ghDist (XiVtx system level)
    (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) ≤ _
  have comparison := ghDist_le_of_approx_subsets
    (s := (univ : Set (XiVtx system level)))
    (fun vertex => xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex.val)
    (ε₁ := 0) (ε₂ := tolerance)
    (ε₃ := xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1))
    (fun vertex => ⟨vertex, mem_univ _, by simp only [dist_self, le_refl]⟩)
    (fun point => by
      obtain ⟨vertex, bound⟩ := xiCompletion_finite_net system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair level point
      exact ⟨⟨vertex, mem_univ _⟩, bound⟩)
    (fun first second => by
      change |dist first.val second.val - dist _ _| ≤ tolerance
      rw [xiNormalizedUnitLevel_dist_eq system connected loopless rate
        (zero_lt_one.trans rateGreaterThanOne) scale scalePositive]
      have weightedDistance : dist
          (xiCompletionEmbedding system connected lengths lengthsPositive rate
            (zero_lt_one.trans rateGreaterThanOne) eigenpair level first.val)
          (xiCompletionEmbedding system connected lengths lengthsPositive rate
            (zero_lt_one.trans rateGreaterThanOne) eigenpair level second.val) =
          xiScaledWeightedDistance system lengths rate level first.val second.val := by
        letI := xiLevelMetricSpace system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) level
        exact (xiCompletionEmbedding_isometry system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level).dist_eq first.val second.val
      rw [weightedDistance]
      exact distortion first.val second.val)
  simpa only [zero_add] using comparison

theorem xiSimpleGraph_gromovHausdorff_limit (system : EIGSData K)
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
    ∃ scale : ℝ, ∃ scalePositive : 0 < scale,
      Tendsto (xiUnitGHPoint system connected rate (zero_lt_one.trans rateGreaterThanOne) scale scalePositive)
        atTop (nhds (xiWeightedLimitGHPoint system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)) := by
  obtain ⟨scale, scalePositive, uniformConvergence⟩ := xiSimpleGraph_uniform_metric_limit system connected
    loopless unique plantingNonadjacent distancePositive lengths lengthsPositive rate rateGreaterThanOne normalized eigenpair
  refine ⟨scale, scalePositive, Metric.tendsto_atTop.mpr ?_⟩
  intro tolerance tolerancePositive
  obtain ⟨distortionThreshold, distortionBound⟩ := uniformConvergence (tolerance * scale)
    (mul_pos tolerancePositive scalePositive)
  have smallRadius := (xiFiniteNetRadius_tendsto_zero system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair).eventually (gt_mem_nhds (half_pos tolerancePositive))
  obtain ⟨radiusThreshold, radiusBound⟩ := eventually_atTop.mp smallRadius
  refine ⟨max distortionThreshold radiusThreshold, ?_⟩
  intro level levelBound
  have levelDistortion : ∀ source sink : XiVtx system level,
      |(((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level) / scale -
        xiScaledWeightedDistance system lengths rate level source sink| ≤ tolerance := by
    intro source sink
    have bound := distortionBound level ((le_max_left _ _).trans levelBound) source sink
    have identity :
        (((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level) / scale -
          xiScaledWeightedDistance system lengths rate level source sink =
        (((XiSimpleGraph system level).dist source sink : ℝ) / rate ^ level -
          scale * xiScaledWeightedDistance system lengths rate level source sink) / scale := by
      field_simp <;> ring
    rw [identity, abs_div, abs_of_pos scalePositive]
    exact ((div_lt_iff₀ scalePositive).mpr bound).le
  have ghBound := xiUnitGHPoint_dist_le system connected loopless lengths lengthsPositive rate
    rateGreaterThanOne eigenpair scale scalePositive level tolerance levelDistortion
  have meshBound := radiusBound level ((le_max_right _ _).trans levelBound)
  linarith

end EIGS

#print axioms EIGS.xiSimpleGraph_gromovHausdorff_limit
