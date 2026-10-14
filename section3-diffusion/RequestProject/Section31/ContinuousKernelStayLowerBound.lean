import RequestProject.Section31.ContinuousKernelHalfTimeDiagonal
import RequestProject.Section31.FinitePartitionL2Average

/-! A continuous local test with positive semigroup expectation forces the
same heat diagonal to be large. The proof uses an L2 Riesz row, not point
evaluation on the closed form domain. An actual-model consumer must prove
the test expectation from its finite-walk stay estimate. Candidate source. -/

namespace IGS.Sec31
open MeasureTheory Filter Topology
open scoped NNReal
noncomputable section
set_option maxHeartbeats 2000000

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space] (law : Measure Space) [IsFiniteMeasure law]

theorem continuousLocalTest_L2_norm_sq_le_measure
    (embedding : C(Space, ℝ) →L[ℝ] Lp ℝ 2 law)
    (embeddingAE : ∀ function : C(Space, ℝ), (embedding function : Space → ℝ) =ᵐ[law] function)
    (test : C(Space, ℝ)) (region : Set Space) (regionMeasurable : MeasurableSet region)
    (testBounds : ∀ point, 0 ≤ test point ∧ test point ≤ 1)
    (vanishes : ∀ point ∉ region, test point = 0) :
    ‖embedding test‖ ^ 2 ≤ law.real region := by
  have squareIntegrable : Integrable (fun point => test point ^ 2) law := by
    apply Integrable.of_bound (test.continuous.measurable.pow_const 2).aestronglyMeasurable 1
    exact Eventually.of_forall fun point => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      obtain ⟨nonnegative, atMostOne⟩ := testBounds point
      nlinarith [mul_nonneg nonnegative (sub_nonneg.mpr atMostOne)]
  have comparison (point : Space) : test point ^ 2 ≤ region.indicator (fun _ => (1 : ℝ)) point := by
    by_cases belongs : point ∈ region
    · rw [Set.indicator_of_mem belongs]
      obtain ⟨nonnegative, atMostOne⟩ := testBounds point
      nlinarith [mul_nonneg nonnegative (sub_nonneg.mpr atMostOne)]
    · rw [Set.indicator_of_notMem belongs, vanishes point belongs]
      norm_num
  calc
    ‖embedding test‖ ^ 2 = ∫ point, test point ^ 2 ∂law := by
      rw [L2_norm_sq_eq_integral_square]
      exact integral_congr_ae ((embeddingAE test).mono (fun point equality => congrArg (fun value : ℝ => value ^ 2) equality))
    _ ≤ ∫ point, region.indicator (fun _ => (1 : ℝ)) point ∂law :=
      integral_mono squareIntegrable ((integrable_const (1 : ℝ)).indicator regionMeasurable) comparison
    _ = law.real region := integral_indicator_one regionMeasurable

theorem continuousOperatorKernelRow_norm_sq_lower_of_test
    (operator : Lp ℝ 2 law →L[ℝ] C(Space, ℝ)) (point : Space) (test : Lp ℝ 2 law)
    (probability volume : ℝ) (probabilityNonnegative : 0 ≤ probability) (volumePositive : 0 < volume)
    (testExpectation : probability ≤ operator test point) (testNormBound : ‖test‖ ^ 2 ≤ volume) :
    probability ^ 2 / volume ≤ ‖continuousOperatorKernelRow operator point‖ ^ 2 := by
  have cauchy := real_inner_mul_inner_self_le (continuousOperatorKernelRow operator point) test
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    ← continuousOperatorKernelRow_represents operator point test] at cauchy
  have cauchySquared : operator test point ^ 2 ≤
      ‖continuousOperatorKernelRow operator point‖ ^ 2 * ‖test‖ ^ 2 := by
    simpa only [pow_two] using cauchy
  have squaredExpectation : probability ^ 2 ≤ operator test point ^ 2 := by
    nlinarith [testExpectation, probabilityNonnegative]
  have productBound : probability ^ 2 ≤ ‖continuousOperatorKernelRow operator point‖ ^ 2 * volume := by
    exact squaredExpectation.trans (cauchySquared.trans
      (mul_le_mul_of_nonneg_left testNormBound (sq_nonneg _)))
  exact (div_le_iff₀ volumePositive).mpr productBound

theorem continuousKernel_diagonal_lower_of_local_test [law.IsOpenPosMeasure]
    (domain : Submodule ℝ (Lp ℝ 2 law)) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values)
    (closable : QuadraticEnergySpace.SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set (Lp ℝ 2 law)))
    (embedding : C(Space, ℝ) →L[ℝ] Lp ℝ 2 law)
    (embeddingInjective : Function.Injective embedding)
    (embeddingAE : ∀ function : C(Space, ℝ), (embedding function : Space → ℝ) =ᵐ[law] function)
    (time : ℝ≥0) (halfLift fullLift : Lp ℝ 2 law →L[ℝ] C(Space, ℝ))
    (halfCompact : IsCompactOperator halfLift)
    (halfCompatibility : ∀ forcing, embedding (halfLift forcing) =
      QuadraticEnergySpace.closedSemigroup domain form nonnegative closable domainDense (time / 2) forcing)
    (fullCompatibility : ∀ forcing, embedding (fullLift forcing) =
      QuadraticEnergySpace.closedSemigroup domain form nonnegative closable domainDense time forcing)
    (continuousOperator : C(Space, ℝ) →L[ℝ] C(Space, ℝ))
    (continuousCompatibility : ∀ function, embedding (continuousOperator function) =
      QuadraticEnergySpace.closedSemigroup domain form nonnegative closable domainDense (time / 2) (embedding function))
    (kernel : Space → Space → ℝ)
    (kernelContinuous : Continuous (fun points : Space × Space => kernel points.1 points.2))
    (representation : ∀ forcing point, fullLift forcing point = ∫ other, kernel point other * forcing other ∂law)
    (point : Space) (test : C(Space, ℝ)) (region : Set Space) (regionMeasurable : MeasurableSet region)
    (volumePositive : 0 < law.real region)
    (testBounds : ∀ point, 0 ≤ test point ∧ test point ≤ 1)
    (vanishes : ∀ point ∉ region, test point = 0)
    (probability : ℝ) (probabilityNonnegative : 0 ≤ probability)
    (testExpectation : probability ≤ continuousOperator test point) :
    probability ^ 2 / law.real region ≤ kernel point point := by
  have sameLift : halfLift (embedding test) = continuousOperator test := by
    apply embeddingInjective
    rw [halfCompatibility, continuousCompatibility]
  rw [continuousKernel_diagonal_eq_half_time_row law domain form nonnegative closable domainDense
    embedding embeddingInjective embeddingAE time halfLift fullLift halfCompact halfCompatibility
    fullCompatibility kernel kernelContinuous representation point]
  apply continuousOperatorKernelRow_norm_sq_lower_of_test law halfLift point (embedding test)
    probability (law.real region) probabilityNonnegative volumePositive
  · rw [sameLift]
    exact testExpectation
  · exact continuousLocalTest_L2_norm_sq_le_measure law embedding embeddingAE test region regionMeasurable testBounds vanishes

end
end IGS.Sec31

#print axioms IGS.Sec31.continuousLocalTest_L2_norm_sq_le_measure
#print axioms IGS.Sec31.continuousOperatorKernelRow_norm_sq_lower_of_test
#print axioms IGS.Sec31.continuousKernel_diagonal_lower_of_local_test
