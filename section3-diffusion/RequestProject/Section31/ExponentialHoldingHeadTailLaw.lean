import RequestProject.Section31.ExponentialHoldingPrefixTailIndependence

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory
noncomputable section

def prependHoldingTime (first : ℝ) (tail : ℕ → ℝ) : ℕ → ℝ
  | 0 => first
  | index + 1 => tail index

theorem prependHoldingTime_measurable :
    Measurable (fun pair : ℝ × (ℕ → ℝ) => prependHoldingTime pair.1 pair.2) := by
  apply measurable_pi_lambda
  intro index
  cases index with
  | zero => exact measurable_fst
  | succ index => exact (measurable_pi_apply index).comp measurable_snd

theorem exponential_holding_head_tail_map :
    exponentialHoldingTimeLaw.map
        (fun holdingTimes => (holdingTimes 0, shiftedHoldingTimes 1 holdingTimes)) =
      (expMeasure 1).prod exponentialHoldingTimeLaw := by
  have independent := (exponential_holding_prefix_tail_independent 1).comp
    (measurable_pi_apply (0 : Fin 1)) measurable_id
  have independentHead : IndepFun (fun holdingTimes : ℕ → ℝ => holdingTimes 0)
      (shiftedHoldingTimes 1) exponentialHoldingTimeLaw := by
    simpa only [Function.comp_def, Fin.val_zero, id_eq] using independent
  have mapped := (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable (shiftedHoldingTimes_measurable 1).aemeasurable).mp
      independentHead
  rw [exponentialHoldingTimeLaw_eval, (shiftedHoldingTimes_hasLaw 1).map_eq] at mapped
  exact mapped

theorem exponential_holding_prepend_map :
    ((expMeasure 1).prod exponentialHoldingTimeLaw).map
      (fun pair => prependHoldingTime pair.1 pair.2) = exponentialHoldingTimeLaw := by
  rw [← exponential_holding_head_tail_map,
    Measure.map_map prependHoldingTime_measurable
      ((measurable_pi_apply 0).prodMk (shiftedHoldingTimes_measurable 1))]
  have reconstruction :
      (fun holdingTimes : ℕ → ℝ =>
        prependHoldingTime (holdingTimes 0) (shiftedHoldingTimes 1 holdingTimes)) = id := by
    funext holdingTimes index
    cases index with
    | zero => rfl
    | succ index => simp only [prependHoldingTime, shiftedHoldingTimes, Nat.add_comm, id_eq]
  change exponentialHoldingTimeLaw.map
    (fun holdingTimes => prependHoldingTime (holdingTimes 0)
      (shiftedHoldingTimes 1 holdingTimes)) = exponentialHoldingTimeLaw
  rw [reconstruction, Measure.map_id]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.prependHoldingTime_measurable
#print axioms IGS.Sec31.PoissonClock.exponential_holding_head_tail_map
#print axioms IGS.Sec31.PoissonClock.exponential_holding_prepend_map
