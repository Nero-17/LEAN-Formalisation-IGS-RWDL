import RequestProject.Section31.EIGSDHLLetterAddressLaw
import RequestProject.Section31.EIGSDHLRetainedStarBallMass
import RequestProject.Section31.RenewalPhaseEndpointCost
import RequestProject.Section31.MetricBallMassMeasurable

/-! Almost every actual DHL completion point has large volume at arbitrarily
fine cell scales. The retained degree gain is proved from successful iid
words, then transferred through the exact actual address law. This is a
volume fluctuation theorem; it makes no heat-kernel optimality assertion. -/

namespace EIGS
open MeasureTheory ProbabilityTheory Filter Topology IGS.Sec31
noncomputable section

theorem exists_dhl_ae_infinite_geometric_volume_lower
    (connected : ∀ colour, (ruleSG (flowerSystem 2 2) colour).Connected)
    (lengths : Fin 1 → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : ((flowerSystem 2 2).ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters (flowerSystem 2 2)) :
    ∃ coefficient radiusFactor : ℝ, 0 < coefficient ∧ 0 < radiusFactor ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
        ∀ᵐ point ∂xiLimitMeasure (flowerSystem 2 2) connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass,
          ∀ threshold : ℕ, ∃ level : ℕ, threshold ≤ level ∧
            coefficient * (level : ℝ) ^ (1 - epsilon) / (4 : ℝ) ^ level ≤
              (xiLimitMeasure (flowerSystem 2 2) connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
                (Metric.ball point (radiusFactor * rate⁻¹ ^ level)) := by
  letI := xiCompletion_compactSpace (flowerSystem 2 2) connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  obtain ⟨coefficient, radiusFactor, coefficientPositive, radiusPositive, starLower⟩ :=
    exists_dhlRetainedStarBallMassLower connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
  have massRateIdentity : mass.rate = 4 := by
    rw [XiMassParameters.rate_eq_spectralRadius, flowerSystem_massSpectralRadius]
    norm_num
  refine ⟨coefficient, radiusFactor, coefficientPositive, radiusPositive, ?_⟩
  intro epsilon epsilonPositive epsilonBelowOne
  have measurableGood : MeasurableSet
      {point | ∀ threshold : ℕ, ∃ level : ℕ, threshold ≤ level ∧
        coefficient * (level : ℝ) ^ (1 - epsilon) / (4 : ℝ) ^ level ≤
          (xiLimitMeasure (flowerSystem 2 2) connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
            (Metric.ball point (radiusFactor * rate⁻¹ ^ level))} := by
    simp only [Set.setOf_forall, Set.setOf_exists, Set.setOf_and]
    apply MeasurableSet.iInter
    intro threshold
    apply MeasurableSet.iUnion
    intro level
    apply MeasurableSet.inter
    · by_cases large : threshold ≤ level <;> simp [large]
    · exact measurableSet_le measurable_const
        (measurable_real_ball_mass
          (xiLimitMeasure (flowerSystem 2 2) connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
          (radiusFactor * rate⁻¹ ^ level))
  have sampleGood : ∀ᵐ sample ∂Measure.infinitePi (fun _ : ℕ => dhlLetterLaw),
      ∀ threshold : ℕ, ∃ level : ℕ, threshold ≤ level ∧
        coefficient * (level : ℝ) ^ (1 - epsilon) / (4 : ℝ) ^ level ≤
          (xiLimitMeasure (flowerSystem 2 2) connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
            (Metric.ball (xiAddressLimit (flowerSystem 2 2) connected lengths lengthsPositive rate
              rateGreaterThanOne eigenpair (dhlAddressOfLetters sample)) (radiusFactor * rate⁻¹ ^ level)) := by
    filter_upwards [dhlLetters_ae_eventually_retention_phase] with sample successful
    intro threshold
    have eventual := successful.and
      ((eventually_renewal_endpoint_power_cost epsilon epsilonPositive epsilonBelowOne).and
        (eventually_ge_atTop threshold))
    obtain ⟨width, ⟨trial, success⟩, powerCost, widthLarge⟩ := eventual.exists
    let offset := trial.val * width
    let level := offset + width
    have levelIdentity : level = (trial.val + 1) * width := by dsimp [level, offset]; ring
    have levelLarge : threshold ≤ level := widthLarge.trans (by dsimp [level]; omega)
    have endpointUpper : level ≤ (width + 1) ^ 3 * 2 ^ width := by
      rw [levelIdentity]
      exact (renewal_word_endpoint_bounds width trial).2
    have gain : (level : ℝ) ^ (1 - epsilon) ≤ (2 : ℝ) ^ width := powerCost level endpointUpper
    have successShift : independentWordBlock width offset 0 sample ∈ dhlGoodRetentionWords width false := by
      simpa only [independentWordBlock, offset, zero_mul, zero_add, add_zero] using success
    have incident := dhlLetters_retention_block_incident sample offset width successShift
    have physicalLower := starLower offset width
      (XiTail (flowerSystem 2 2) offset
        (xiAddressEdge (flowerSystem 2 2) offset (dhlAddressOfLetters sample)))
      (dhlAddressOfLetters sample) incident
    rw [massRateIdentity] at physicalLower
    refine ⟨level, levelLarge, ?_⟩
    calc
      coefficient * (level : ℝ) ^ (1 - epsilon) / (4 : ℝ) ^ level =
          coefficient / (4 : ℝ) ^ level * (level : ℝ) ^ (1 - epsilon) := by ring
      _ ≤ coefficient / (4 : ℝ) ^ level * (2 : ℝ) ^ width :=
        mul_le_mul_of_nonneg_left gain (by positivity)
      _ ≤ _ := physicalLower
  have mappedGood := (ae_map_iff
    ((measurable_xiAddressLimit (flowerSystem 2 2) connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair).comp measurable_dhlAddressOfLetters).aemeasurable measurableGood).mpr sampleGood
  have pointLaw : (Measure.infinitePi (fun _ : ℕ => dhlLetterLaw)).map
      ((xiAddressLimit (flowerSystem 2 2) connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) ∘
        dhlAddressOfLetters) =
      xiLimitMeasure (flowerSystem 2 2) connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass := by
    rw [← Measure.map_map
      (measurable_xiAddressLimit (flowerSystem 2 2) connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
      measurable_dhlAddressOfLetters, dhlLetters_map_addressMeasure]
    rfl
  rw [pointLaw] at mappedGood
  exact mappedGood

end
end EIGS

#print axioms EIGS.exists_dhl_ae_infinite_geometric_volume_lower

