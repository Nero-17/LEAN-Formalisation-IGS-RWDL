import RequestProject.Section31.VaryingL2Core

/-! Uniform convergence of continuous functions yields genuine varying-L²
strong convergence for the constructed probability-measure core. -/

namespace IGS.Sec31

set_option maxHeartbeats 2000000

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

theorem VaryingHilbertCore.strong_of_norm_sub_tendsto_zero
    {Core Hilbert : Type*} [AddCommGroup Core] [Module ℝ Core]
    [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    {LevelHilbert : ℕ → Type*}
    [∀ level, NormedAddCommGroup (LevelHilbert level)]
    [∀ level, InnerProductSpace ℝ (LevelHilbert level)]
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (first second : ∀ level, LevelHilbert level) (limit : Hilbert)
    (second_converges : core.Strong second limit)
    (difference_vanishes : Tendsto (fun level => ‖first level - second level‖) atTop (𝓝 0)) :
    core.Strong first limit := by
  intro tolerance positive
  obtain ⟨element, limit_close, second_close⟩ := second_converges (tolerance / 2) (half_pos positive)
  refine ⟨element, limit_close.trans (by linarith), ?_⟩
  filter_upwards [second_close,
    (tendsto_order.1 difference_vanishes).2 (tolerance / 2) (half_pos positive)]
      with level second_close difference_small
  calc
    ‖first level - core.restrict level element‖ ≤
        ‖first level - second level‖ + ‖second level - core.restrict level element‖ :=
      by
        calc
          _ = ‖(first level - second level) + (second level - core.restrict level element)‖ :=
            congrArg norm (sub_add_sub_cancel _ _ _).symm
          _ ≤ _ := norm_add_le _ _
    _ < tolerance := by linarith

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

theorem boundedContinuous_L2_norm_le_sup
    (measure : ProbabilityMeasure Space) (function : Space →ᵇ ℝ) :
    ‖BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ function‖ ≤ ‖function‖ := by
  have mass_one : measureUnivNNReal (measure : Measure Space) = 1 := by
    simp [measureUnivNNReal]
  simpa only [mass_one, NNReal.coe_one, Real.one_rpow, one_mul] using
    (BoundedContinuousFunction.Lp_norm_le (p := 2) (μ := (measure : Measure Space)) function)

theorem uniformly_convergent_functions_L2_strong
    (measures : ℕ → ProbabilityMeasure Space) (measure : ProbabilityMeasure Space)
    (weak_convergence : Tendsto measures atTop (𝓝 measure))
    (functions : ℕ → Space →ᵇ ℝ) (function : Space →ᵇ ℝ)
    (uniform_convergence : Tendsto functions atTop (𝓝 function)) :
    (probabilityL2Core measures measure weak_convergence).Strong
      (fun level => BoundedContinuousFunction.toLp 2 (measures level : Measure Space) ℝ (functions level))
      (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ function) := by
  apply (probabilityL2Core measures measure weak_convergence).strong_of_norm_sub_tendsto_zero
    _ (fun level => BoundedContinuousFunction.toLp 2 (measures level : Measure Space) ℝ function)
    _ (probabilityL2Core_restrictions_strong measures measure weak_convergence function)
  have sup_error := (uniform_convergence.sub (tendsto_const_nhds (x := function))).norm
  have zero_error : Tendsto (fun level => ‖functions level - function‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using sup_error
  apply squeeze_zero (fun _ => norm_nonneg _) _ zero_error
  intro level
  simpa only [map_sub] using boundedContinuous_L2_norm_le_sup (measures level) (functions level - function)

end IGS.Sec31
