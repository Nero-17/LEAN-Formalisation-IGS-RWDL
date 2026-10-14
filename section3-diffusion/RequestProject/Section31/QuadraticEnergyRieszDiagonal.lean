import RequestProject.Section31.QuadraticEnergySemigroupEvaluationBound
import RequestProject.Section31.CompactContinuousKernelRows
import RequestProject.Section31.GeometricDiagonalHeatUpper

/-! The diagonal made from half-time Riesz rows satisfies a point-energy
recurrence for the actual constructed closed semigroup. Its positive-time
energy and contraction estimates are proved internally. The concrete model
must supply the point evaluation and its continuous-representative agreement. -/

namespace IGS.Sec31.QuadraticEnergySpace

open scoped NNReal
noncomputable section

variable {Hilbert Space : Type*} [NormedAddCommGroup Hilbert]
    [InnerProductSpace ℝ Hilbert] [CompleteSpace Hilbert]
    [MetricSpace Space] [CompactSpace Space]

theorem closedSemigroup_riesz_diagonal_recurrence
    (domain : Submodule ℝ Hilbert) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set Hilbert))
    (embedding : C(Space, ℝ) →L[ℝ] Hilbert)
    (evaluation : closedDomain domain form nonnegative →ₗ[ℝ] ℝ) (point : Space)
    (evaluationAgreement : ∀ (target : closedDomain domain form nonnegative)
      (representative : C(Space, ℝ)), embedding representative = target.val →
        evaluation target = representative point)
    (normCoefficient energyCoefficient : ℕ → ℝ)
    (normNonnegative : ∀ level, 0 ≤ normCoefficient level)
    (energyNonnegative : ∀ level, 0 ≤ energyCoefficient level)
    (evaluationBounds : ∀ level (target : closedDomain domain form nonnegative),
      evaluation target ^ 2 ≤ normCoefficient level * ‖target.val‖ ^ 2 +
        energyCoefficient level * closedForm domain form nonnegative closable target)
    (time : ℝ≥0) (timePositive : 0 < time)
    (smoothing : Hilbert →L[ℝ] C(Space, ℝ))
    (compatibility : ∀ forcing, embedding (smoothing forcing) =
      closedSemigroup domain form nonnegative closable domainDense (time / 2) forcing) :
    ∀ level, (‖continuousOperatorKernelRow smoothing point‖ ^ 2) ^ 2 ≤
      (normCoefficient level + energyCoefficient level / (time : ℝ)) *
        ‖continuousOperatorKernelRow smoothing point‖ ^ 2 := by
  let row := continuousOperatorKernelRow smoothing point
  obtain ⟨lifted, liftedEquality, energyBound⟩ :=
    closedSemigroup_exists_energy_bound domain form nonnegative closable domainDense
      (time / 2) (by positivity) row
  have evaluationEquality : evaluation lifted = ‖row‖ ^ 2 := by
    calc
      evaluation lifted = smoothing row point := evaluationAgreement lifted (smoothing row) (by
        rw [compatibility, ← liftedEquality])
      _ = inner ℝ row row := continuousOperatorKernelRow_represents smoothing point row
      _ = ‖row‖ ^ 2 := real_inner_self_eq_norm_sq row
  have normBound : ‖lifted.val‖ ≤ ‖row‖ := by
    rw [liftedEquality]
    calc
      _ ≤ ‖closedSemigroup domain form nonnegative closable domainDense (time / 2)‖ * ‖row‖ :=
        (closedSemigroup domain form nonnegative closable domainDense (time / 2)).le_opNorm row
      _ ≤ 1 * ‖row‖ := mul_le_mul_of_nonneg_right
        (closedSemigroup_norm domain form nonnegative closable domainDense (time / 2)) (norm_nonneg row)
      _ = ‖row‖ := one_mul _
  have squaredNormBound : ‖lifted.val‖ ^ 2 ≤ ‖row‖ ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg lifted.val) normBound
  have denominator : (2 : ℝ) * ((time / 2 : ℝ≥0) : ℝ) = (time : ℝ) := by
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    ring
  rw [denominator] at energyBound
  intro level
  have pointBound := evaluationBounds level lifted
  rw [evaluationEquality] at pointBound
  calc
    (‖row‖ ^ 2) ^ 2 ≤ normCoefficient level * ‖lifted.val‖ ^ 2 +
        energyCoefficient level * closedForm domain form nonnegative closable lifted := pointBound
    _ ≤ normCoefficient level * ‖row‖ ^ 2 + energyCoefficient level * (‖row‖ ^ 2 / (time : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left squaredNormBound (normNonnegative level))
        (mul_le_mul_of_nonneg_left energyBound (energyNonnegative level))
    _ = (normCoefficient level + energyCoefficient level / (time : ℝ)) * ‖row‖ ^ 2 := by ring

end
end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_riesz_diagonal_recurrence
