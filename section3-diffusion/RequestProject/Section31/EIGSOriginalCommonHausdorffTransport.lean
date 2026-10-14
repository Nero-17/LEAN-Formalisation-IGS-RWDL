import RequestProject.Section31.CommonRealisationMeasuredTransport
import RequestProject.Section31.EIGSOriginalCountableRealisation

/-! Hausdorff convergence in the same countable common realization.
The actual weighted-completion finite net is divided by the actual positive
completion diameter. Equality of native and normalized distances is not used. -/

namespace EIGS.MeasuredGHP
noncomputable section
open MeasureTheory Filter Topology Metric Set IGS.Sec31
open scoped Classical
variable {K : ℕ}

 theorem xiOriginalCommon_hausdorffDist_tendsto_zero
    (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    {Ambient : Type*} [MetricSpace Ambient]
    (target : XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair → Ambient)
    (targetIsometry : letI originalCommonHausdorffStatementMetric :=
      xiCompletionDiameterMetricSpace system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair
      Isometry target)
    (sources : ∀ level, XiVtx system level → Ambient)
    (radii : ℕ → ℝ) (radiiNonnegative : ∀ level, 0 ≤ radii level)
    (radiiZero : Tendsto radii atTop (𝓝 0))
    (displacement : ∀ level vertex,
      dist (sources level vertex) (target (xiCompletionEmbedding system connected lengths
        lengthsPositive rate (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex)) ≤ radii level) :
    Tendsto (fun level => hausdorffDist (range (sources level)) (range target))
      atTop (𝓝 0) := by
  let nativeMetric : MetricSpace (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) := inferInstance
  have nativeNet := xiCompletion_finite_net system connected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair
  have nativeMeshNonnegative (level : ℕ) :
      0 ≤ xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1) := by
    obtain ⟨vertex, bound⟩ := nativeNet level
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair 0 true)
    exact dist_nonneg.trans bound
  have diameterPositive := xiCompletionDiameter_positive system connected lengths lengthsPositive
    rate rateGreaterThanOne eigenpair
  have normalizedMeshZero : Tendsto (fun level =>
      (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1)) /
        xiCompletionDiameter system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair) atTop (𝓝 0) := by
    simpa only [zero_div] using
      (xiFiniteNetRadius_tendsto_zero system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair).div_const
          (xiCompletionDiameter system connected lengths lengthsPositive rate
            (zero_lt_one.trans rateGreaterThanOne) eigenpair)
  letI originalCommonHausdorffProofMetric := xiCompletionDiameterMetricSpace system connected
    lengths lengthsPositive rate rateGreaterThanOne eigenpair
  have normalizedNet (level : ℕ) (point : XiMetricCompletion system connected lengths
      lengthsPositive rate (zero_lt_one.trans rateGreaterThanOne) eigenpair) :
      ∃ vertex : XiVtx system level,
        dist point (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex) ≤
          (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1)) /
            xiCompletionDiameter system connected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair := by
    obtain ⟨vertex, bound⟩ := nativeNet level point
    refine ⟨vertex, ?_⟩
    change (xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair)⁻¹ *
      @dist _ nativeMetric.toDist point (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex) ≤ _
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right bound (inv_nonneg.mpr diameterPositive.le)
  exact commonRealisation_hausdorffDist_tendsto_zero
    (xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) target targetIsometry sources radii
    (fun level => (xiRuleRadius system lengths / (1 - rate⁻¹) * rate⁻¹ ^ (level + 1)) /
      xiCompletionDiameter system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair)
    radiiNonnegative (fun level => div_nonneg (nativeMeshNonnegative level) diameterPositive.le)
    radiiZero normalizedMeshZero displacement normalizedNet

end
end EIGS.MeasuredGHP

#print axioms EIGS.MeasuredGHP.xiOriginalCommon_hausdorffDist_tendsto_zero
