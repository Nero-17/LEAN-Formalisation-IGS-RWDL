import RequestProject.Section31.ExponentialHoldingHeadTailLaw
import RequestProject.Section31.ExponentialMemorylessResidualLaw

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

/-- Survival of the first holding time leaves the entire regenerated
infinite sequence with its original iid law, weighted by survival. -/
theorem exponential_residual_sequence_measure
    (elapsed : ℝ) (elapsedNonnegative : 0 ≤ elapsed) :
    (((expMeasure 1).prod exponentialHoldingTimeLaw).restrict
      (Ioi elapsed ×ˢ univ)).map
        (fun pair => prependHoldingTime (pair.1 - elapsed) pair.2) =
      ENNReal.ofReal (Real.exp (-elapsed)) • exponentialHoldingTimeLaw := by
  have shiftMeasurable : Measurable (fun value : ℝ => value - elapsed) :=
    measurable_id.sub measurable_const
  have productMap :
      (((expMeasure 1).restrict (Ioi elapsed)).prod exponentialHoldingTimeLaw).map
          (Prod.map (fun value : ℝ => value - elapsed) id) =
        (((expMeasure 1).restrict (Ioi elapsed)).map (fun value => value - elapsed)).prod
          exponentialHoldingTimeLaw := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map ((expMeasure 1).restrict (Ioi elapsed))
        exponentialHoldingTimeLaw shiftMeasurable measurable_id).symm
  rw [← Measure.restrict_prod_eq_prod_univ]
  have compositionEquality :
      (fun pair : ℝ × (ℕ → ℝ) => prependHoldingTime (pair.1 - elapsed) pair.2) =
        (fun pair => prependHoldingTime pair.1 pair.2) ∘
          Prod.map (fun value : ℝ => value - elapsed) id := rfl
  rw [compositionEquality, ← Measure.map_map prependHoldingTime_measurable
    (shiftMeasurable.prodMap measurable_id), productMap,
    unit_exponential_surviving_residual_measure elapsed elapsedNonnegative,
    Measure.prod_smul_left, Measure.map_smul, exponential_holding_prepend_map]

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.exponential_residual_sequence_measure
