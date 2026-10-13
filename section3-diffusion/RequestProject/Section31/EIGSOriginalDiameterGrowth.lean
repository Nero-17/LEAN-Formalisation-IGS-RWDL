import RequestProject.Section31.EIGSDiameterOfRules

/-! Two-sided geometric growth of the actual original unit-graph diameter,
deduced from its positive normalized metric-space diameter limit. -/

namespace EIGS

open Filter Topology Metric Set

variable {K : ℕ}

theorem xiFiniteLevelDiameter_unit_scale (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (rate : ℝ) (rate_positive : 0 < rate) (scale : ℝ) (scale_positive : 0 < scale)
    (level : ℕ) :
    xiFiniteLevelDiameter system connected (fun _ => scale⁻¹)
      (fun _ => inv_pos.mpr scale_positive) rate rate_positive level =
      (rate⁻¹ ^ level * scale⁻¹) *
        xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level := by
  letI := xiLevelMetricSpace system connected (fun _ => (1 : ℝ)⁻¹)
    (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level
  have level_scale_positive : 0 < rate⁻¹ ^ level * scale⁻¹ :=
    mul_pos (pow_pos (inv_pos.mpr rate_positive) _) (inv_pos.mpr scale_positive)
  have metric_equality : positiveScaledMetricSpace (XiVtx system level)
      (rate⁻¹ ^ level * scale⁻¹) level_scale_positive =
      xiLevelMetricSpace system connected (fun _ => scale⁻¹)
        (fun _ => inv_pos.mpr scale_positive) rate rate_positive level := by
    apply MetricSpace.ext
    ext source sink
    change (rate⁻¹ ^ level * scale⁻¹) *
        ((1 : ℝ)⁻¹ ^ level * (XiNetwork system level).weightedDistance
          (fun _ => (1 : ℝ)⁻¹) source sink) =
      rate⁻¹ ^ level * (XiNetwork system level).weightedDistance (fun _ => scale⁻¹) source sink
    have lengths_equality : (fun _ : Fin K => scale⁻¹) = scale⁻¹ • (fun _ : Fin K => (1 : ℝ)) := by
      ext colour
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    rw [lengths_equality, Network.weightedDistance_smul _ _ (inv_nonneg.mpr scale_positive.le)]
    simp only [inv_one, one_pow, one_mul]
    ring
  have diameter_equality := congrArg
    (fun metric : MetricSpace (XiVtx system level) =>
      @Metric.diam (XiVtx system level) metric.toPseudoMetricSpace Set.univ) metric_equality
  exact diameter_equality.symm.trans
    (positiveScaledMetricSpace_diameter (XiVtx system level)
      (rate⁻¹ ^ level * scale⁻¹) level_scale_positive)

theorem xiOriginalDiameter_spectral_growth (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ᶠ level in atTop,
      lower * (system.distanceSpectralRadius connected) ^ level ≤
        xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level ∧
      xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level ≤
        upper * (system.distanceSpectralRadius connected) ^ level := by
  let parameters := xiPathMetricDataOfRules system connected loopless unique distance_positive
  have rate_gt_one : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique planting_nonadjacent distance_positive)
  obtain ⟨scale, scale_positive, _, convergence⟩ := xiSimpleGraph_normalized_diameter_limit system
    connected loopless unique planting_nonadjacent distance_positive parameters.lengths
    parameters.lengthsPositive (system.distanceSpectralRadius connected) rate_gt_one
    parameters.normalized parameters.eigenpair
  have limit_positive := xiCompletionDiameter_positive system connected parameters.lengths
    parameters.lengthsPositive (system.distanceSpectralRadius connected) rate_gt_one parameters.eigenpair
  refine ⟨scale * xiCompletionDiameter system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) (zero_lt_one.trans rate_gt_one) parameters.eigenpair / 2,
    scale * (2 * xiCompletionDiameter system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) (zero_lt_one.trans rate_gt_one) parameters.eigenpair),
    by positivity, by positivity, ?_⟩
  have eventually_lower := convergence.eventually (lt_mem_nhds (by linarith :
    xiCompletionDiameter system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) (zero_lt_one.trans rate_gt_one) parameters.eigenpair / 2 <
    xiCompletionDiameter system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) (zero_lt_one.trans rate_gt_one) parameters.eigenpair))
  have eventually_upper := convergence.eventually (gt_mem_nhds (by linarith :
    xiCompletionDiameter system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) (zero_lt_one.trans rate_gt_one) parameters.eigenpair <
    2 * xiCompletionDiameter system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) (zero_lt_one.trans rate_gt_one) parameters.eigenpair))
  filter_upwards [eventually_lower, eventually_upper] with level lower_bound upper_bound
  rw [xiFiniteLevelDiameter_unit_scale system connected _ _ scale scale_positive level]
    at lower_bound upper_bound
  have power_positive : 0 < (system.distanceSpectralRadius connected) ^ level :=
    pow_pos (zero_lt_one.trans rate_gt_one) _
  have scale_identity :
      ((system.distanceSpectralRadius connected)⁻¹ ^ level * scale⁻¹) *
        xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level =
      xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level /
        (system.distanceSpectralRadius connected) ^ level / scale := by
    simp only [inv_pow, div_eq_mul_inv]
    ring
  rw [scale_identity] at lower_bound upper_bound
  constructor
  · have bound := (lt_div_iff₀ scale_positive).mp lower_bound
    have bound := (lt_div_iff₀ power_positive).mp bound
    nlinarith
  · have bound := (div_lt_iff₀ scale_positive).mp upper_bound
    have bound := (div_lt_iff₀ power_positive).mp bound
    nlinarith

end EIGS

#print axioms EIGS.xiFiniteLevelDiameter_unit_scale
#print axioms EIGS.xiOriginalDiameter_spectral_growth
