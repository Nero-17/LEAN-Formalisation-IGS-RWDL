import RequestProject.Section31.ExponentialHoldingHeadTailLaw

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 2200000

def holdingPrefix (count : ℕ) (holdingTimes : ℕ → ℝ) : Fin count → ℝ :=
  fun index => holdingTimes index

theorem holdingPrefix_measurable (count : ℕ) : Measurable (holdingPrefix count) := by
  apply measurable_pi_lambda
  intro index
  exact measurable_pi_apply (index : ℕ)

theorem exponential_holding_prefix_tail_map (count : ℕ) :
    exponentialHoldingTimeLaw.map
        (fun holdingTimes => (holdingPrefix count holdingTimes, shiftedHoldingTimes count holdingTimes)) =
      (exponentialHoldingTimeLaw.map (holdingPrefix count)).prod exponentialHoldingTimeLaw := by
  have identity := (indepFun_iff_map_prod_eq_prod_map_map
    (holdingPrefix_measurable count).aemeasurable
    (shiftedHoldingTimes_measurable count).aemeasurable).mp
      (exponential_holding_prefix_tail_independent count)
  rw [(shiftedHoldingTimes_hasLaw count).map_eq] at identity
  exact identity

theorem exponential_holding_prefix_next_tail_map (count : ℕ) :
    exponentialHoldingTimeLaw.map (fun holdingTimes =>
        (holdingPrefix count holdingTimes,
          (holdingTimes count, shiftedHoldingTimes (count + 1) holdingTimes))) =
      (exponentialHoldingTimeLaw.map (holdingPrefix count)).prod
        ((expMeasure 1).prod exponentialHoldingTimeLaw) := by
  letI : IsProbabilityMeasure (exponentialHoldingTimeLaw.map (holdingPrefix count)) :=
    Measure.isProbabilityMeasure_map (holdingPrefix_measurable count).aemeasurable
  have regroup :
      (fun holdingTimes : ℕ → ℝ => (holdingPrefix count holdingTimes,
        (holdingTimes count, shiftedHoldingTimes (count + 1) holdingTimes))) =
      (Prod.map id (fun tail : ℕ → ℝ => (tail 0, shiftedHoldingTimes 1 tail))) ∘
        (fun holdingTimes => (holdingPrefix count holdingTimes, shiftedHoldingTimes count holdingTimes)) := by
    funext holdingTimes
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · simp only [Function.comp_def, Prod.map, id_eq, shiftedHoldingTimes, Nat.add_zero]
      · funext index
        simp only [Function.comp_def, Prod.map, id_eq, shiftedHoldingTimes, Nat.add_assoc]
  rw [regroup, ← Measure.map_map
    (measurable_id.prodMap ((measurable_pi_apply 0).prodMk (shiftedHoldingTimes_measurable 1)))
    ((holdingPrefix_measurable count).prodMk (shiftedHoldingTimes_measurable count)),
    exponential_holding_prefix_tail_map,
    ← Measure.map_prod_map _ _ measurable_id
      ((measurable_pi_apply 0).prodMk (shiftedHoldingTimes_measurable 1)),
    Measure.map_id, exponential_holding_head_tail_map]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingPrefix_measurable
#print axioms IGS.Sec31.PoissonClock.exponential_holding_prefix_tail_map
#print axioms IGS.Sec31.PoissonClock.exponential_holding_prefix_next_tail_map
