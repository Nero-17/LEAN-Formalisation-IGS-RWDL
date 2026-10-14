import RequestProject.Section31.FiniteGraphExponentialHoldingProcess
import RequestProject.Section31.ExponentialInverseClockUniform

/-! Exact coupling identities on the explicitly constructed product sample
space. These identify the renewal walk with the deterministic-floor walk at
the inverse clock; counting-law identification and path tightness remain
separate theorems. -/

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open IGS.Sec31.DiscreteMarkov EIGS
open scoped Topology

def exponentialForwardClock (holdingTimes : ℕ → ℝ) (acceleration time : ℝ) : ℝ :=
  cumulativeHoldingTime holdingTimes ⌊acceleration * time⌋₊ / acceleration

theorem holdingTimePath_forward_clock {Vertex : Type*} (trajectory : ℕ → Vertex)
    (holdingTimes : ℕ → ℝ) (positive : ∀ index, 0 < holdingTimes index)
    (acceleration time : ℝ) (accelerationNonzero : acceleration ≠ 0) :
    holdingTimePath trajectory holdingTimes
      (acceleration * exponentialForwardClock holdingTimes acceleration time) =
        trajectory ⌊acceleration * time⌋₊ := by
  have clockEquality : acceleration * exponentialForwardClock holdingTimes acceleration time =
      cumulativeHoldingTime holdingTimes ⌊acceleration * time⌋₊ := by
    unfold exponentialForwardClock
    field_simp
  rw [clockEquality]
  unfold holdingTimePath
  congr 1
  apply holdingJumpIndex_eq_of_interval holdingTimes (fun index => (positive index).le)
  · exact le_rfl
  · simp only [cumulativeHoldingTime, Finset.sum_range_succ]
    exact lt_add_of_pos_right _ (positive _)

theorem holdingTimePath_inverse_clock {Vertex : Type*} (trajectory : ℕ → Vertex)
    (holdingTimes : ℕ → ℝ) (acceleration time : ℝ)
    (accelerationNonzero : acceleration ≠ 0) :
    trajectory ⌊acceleration *
      ((holdingJumpIndex holdingTimes (acceleration * time) : ℝ) / acceleration)⌋₊ =
        holdingTimePath trajectory holdingTimes (acceleration * time) := by
  rw [mul_div_cancel₀ _ accelerationNonzero, Nat.floor_natCast]
  rfl

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
variable [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]

theorem finiteGraphExponentialSampleLaw_clock_coupling
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (initial : ProbabilityMeasure Vertex) :
    ∀ᵐ sample ∂finiteGraphExponentialSampleLaw graph degreePositive initial,
      (∀ (acceleration time : ℝ), acceleration ≠ 0 →
        holdingTimePath sample.1 sample.2
          (acceleration * exponentialForwardClock sample.2 acceleration time) =
            sample.1 ⌊acceleration * time⌋₊) ∧
      ∀ (acceleration : ℕ → ℝ), (∀ level, 0 < acceleration level) →
        Tendsto acceleration atTop atTop → ∀ horizon : ℝ, 0 ≤ horizon →
          ∀ tolerance : ℝ, 0 < tolerance →
            (∀ᶠ level in atTop, ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
              |exponentialForwardClock sample.2 (acceleration level) time - time| < tolerance) ∧
            (∀ᶠ level in atTop, ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
              |(holdingJumpIndex sample.2 (acceleration level * time) : ℝ) /
                acceleration level - time| < tolerance) := by
  have positive := (Measure.quasiMeasurePreserving_snd
    (μ := pathLaw (finiteGraphTransitionKernel graph degreePositive) (initial : Measure Vertex))
    (ν := exponentialHoldingTimeLaw)).ae exponentialHoldingTimeLaw_positive
  have nonexplosion := (Measure.quasiMeasurePreserving_snd
    (μ := pathLaw (finiteGraphTransitionKernel graph degreePositive) (initial : Measure Vertex))
    (ν := exponentialHoldingTimeLaw)).ae exponentialHoldingTimeLaw_nonexplosion
  have average := (Measure.quasiMeasurePreserving_snd
    (μ := pathLaw (finiteGraphTransitionKernel graph degreePositive) (initial : Measure Vertex))
    (ν := exponentialHoldingTimeLaw)).ae exponentialHoldingTimeLaw_clock_average
  filter_upwards [positive, nonexplosion, average] with sample positive nonexplosion average
  constructor
  · exact fun acceleration time nonzero =>
      holdingTimePath_forward_clock sample.1 sample.2 positive acceleration time nonzero
  · intro acceleration accelerationPositive accelerationDiverges horizon horizonNonnegative tolerance tolerancePositive
    exact ⟨holdingClock_floor_uniform sample.2 average acceleration accelerationPositive accelerationDiverges
      horizon horizonNonnegative tolerance tolerancePositive,
      holdingJumpClock_uniform sample.2 positive nonexplosion average acceleration accelerationPositive
        accelerationDiverges horizon horizonNonnegative tolerance tolerancePositive⟩

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.holdingTimePath_forward_clock
#print axioms IGS.Sec31.PoissonClock.holdingTimePath_inverse_clock
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialSampleLaw_clock_coupling
