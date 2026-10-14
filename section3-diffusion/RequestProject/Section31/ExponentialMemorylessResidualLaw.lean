import RequestProject.Section31.ExponentialHoldingZeroCountProbability

/-! The complete residual-time measure identity for a rate-one exponential
holding time, after survival to a deterministic time. This is stronger than
the equality of a single tail probability. -/

namespace IGS.Sec31.PoissonClock
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
noncomputable section

theorem unit_exponential_negative_tail (time : ℝ) (negative : time < 0) :
    expMeasure 1 (Ioi time) = 1 := by
  apply le_antisymm
  · simpa only [measure_univ] using
      (measure_mono (subset_univ (Ioi time)) : expMeasure 1 (Ioi time) ≤ expMeasure 1 univ)
  · calc
      1 = expMeasure 1 (Ioi 0) := by
        rw [unit_exponential_tail_probability 0 le_rfl]
        norm_num
      _ ≤ expMeasure 1 (Ioi time) := measure_mono (fun _ positive => negative.trans positive)

theorem unit_exponential_surviving_residual_measure
    (elapsed : ℝ) (elapsedNonnegative : 0 ≤ elapsed) :
    ((expMeasure 1).restrict (Ioi elapsed)).map (fun value => value - elapsed) =
      ENNReal.ofReal (Real.exp (-elapsed)) • expMeasure 1 := by
  have shiftMeasurable : Measurable (fun value : ℝ => value - elapsed) :=
    measurable_id.sub measurable_const
  have tailEquality (remaining : ℝ) :
      (((expMeasure 1).restrict (Ioi elapsed)).map (fun value => value - elapsed))
          (Ioi remaining) =
        (ENNReal.ofReal (Real.exp (-elapsed)) • expMeasure 1) (Ioi remaining) := by
    rw [Measure.map_apply shiftMeasurable measurableSet_Ioi,
      Measure.restrict_apply (measurableSet_Ioi.preimage shiftMeasurable)]
    by_cases remainingNonnegative : 0 ≤ remaining
    · have intersectionEquality :
          ((fun value : ℝ => value - elapsed) ⁻¹' Ioi remaining) ∩ Ioi elapsed =
            Ioi (elapsed + remaining) := by
        ext value
        simp only [mem_inter_iff, mem_preimage, mem_Ioi]
        constructor
        · rintro ⟨afterRemaining, _⟩
          linarith
        · intro afterBoth
          constructor <;> linarith
      rw [intersectionEquality, unit_exponential_tail_probability _
        (add_nonneg elapsedNonnegative remainingNonnegative), Measure.smul_apply,
        unit_exponential_tail_probability remaining remainingNonnegative]
      change ENNReal.ofReal (Real.exp (-(elapsed + remaining))) =
        ENNReal.ofReal (Real.exp (-elapsed)) * ENNReal.ofReal (Real.exp (-remaining))
      rw [neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    · have intersectionEquality :
          ((fun value : ℝ => value - elapsed) ⁻¹' Ioi remaining) ∩ Ioi elapsed =
            Ioi elapsed := by
        ext value
        simp only [mem_inter_iff, mem_preimage, mem_Ioi]
        constructor
        · exact And.right
        · intro survived
          exact ⟨by linarith [lt_of_not_ge remainingNonnegative], survived⟩
      rw [intersectionEquality, unit_exponential_tail_probability elapsed elapsedNonnegative,
        Measure.smul_apply, unit_exponential_negative_tail remaining
          (lt_of_not_ge remainingNonnegative)]
      simp
  have totalEquality :
      (((expMeasure 1).restrict (Ioi elapsed)).map (fun value => value - elapsed)) univ =
        (ENNReal.ofReal (Real.exp (-elapsed)) • expMeasure 1) univ := by
    rw [Measure.map_apply shiftMeasurable MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, univ_inter,
      unit_exponential_tail_probability elapsed elapsedNonnegative, Measure.smul_apply,
      measure_univ]
    simp
  apply Measure.ext_of_Iic
  intro remaining
  rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _),
    tailEquality, totalEquality,
    measure_compl measurableSet_Ioi]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.unit_exponential_negative_tail
#print axioms IGS.Sec31.PoissonClock.unit_exponential_surviving_residual_measure
