import RequestProject.Section31.CompactRealCoveringNumberPowerBounds
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! Standard finite covering-number power control supplies the Hausdorff
upper bound, using actual minimal covers of the compact metric space. -/

namespace IGS.Sec31
open MeasureTheory Filter Topology Set Metric
open scoped Classical ENNReal NNReal BigOperators
noncomputable section
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

 theorem hausdorffMeasure_zero_of_coveringNumber_power_upper
    (dimension exponent massConstant radiusThreshold : ℝ)
    (dimensionNonnegative : 0 ≤ dimension) (strictExponent : dimension < exponent)
    (constantPositive : 0 < massConstant) (thresholdPositive : 0 < radiusThreshold)
    (coverUpper : ∀ radius : ℝ, 0 < radius → radius ≤ radiusThreshold →
      realCoveringNumber Space radius ≤ massConstant * radius ^ (-dimension)) :
    Measure.hausdorffMeasure exponent (Set.univ : Set Space) = 0 := by
  have exponentPositive : 0 < exponent := lt_of_le_of_lt dimensionNonnegative strictExponent
  let centers := fun radius : ℝ => Metric.minimalCover (Real.toNNReal radius) (Set.univ : Set Space)
  letI : ∀ radius : ℝ, Fintype (centers radius) := fun radius =>
    (Metric.finite_minimalCover (ε := Real.toNNReal radius) (A := (Set.univ : Set Space))).fintype
  let coverSets := fun radius : ℝ => fun center : centers radius =>
    Metric.closedEBall (center : Space) (ENNReal.ofReal radius)
  have cardinality (radius : ℝ) (radiusPositive : 0 < radius) :
      (Fintype.card (centers radius) : ℝ) = realCoveringNumber Space radius := by
    have finiteCover := compact_coveringNumber_univ_ne_top (Space := Space) (Real.toNNReal radius)
      (Real.toNNReal_pos.mpr radiusPositive)
    have equality := congrArg ENat.toNat (Metric.encard_minimalCover finiteCover)
    have naturalEquality : Fintype.card (centers radius) =
        (Metric.coveringNumber (Real.toNNReal radius) (Set.univ : Set Space)).toNat := by
      simpa only [Set.encard, ENat.card_eq_coe_fintype_card, ENat.toNat_coe] using equality
    change _ = ((Metric.coveringNumber (Real.toNNReal radius) (Set.univ : Set Space)).toNat : ℝ)
    exact_mod_cast naturalEquality
  have costUpper : ∀ᶠ radius : ℝ in 𝓝[>] 0,
      (∑ center : centers radius, Metric.ediam (coverSets radius center) ^ exponent) ≤
        ENNReal.ofReal (massConstant * (2 : ℝ) ^ exponent * radius ^ (exponent - dimension)) := by
    filter_upwards [Ioc_mem_nhdsGT thresholdPositive] with radius radiusInRange
    have radiusPositive : 0 < radius := radiusInRange.1
    have realCost : (Fintype.card (centers radius) : ℝ) * (2 * radius) ^ exponent ≤
        massConstant * (2 : ℝ) ^ exponent * radius ^ (exponent - dimension) := by
      rw [cardinality radius radiusPositive]
      calc
        realCoveringNumber Space radius * (2 * radius) ^ exponent ≤
            (massConstant * radius ^ (-dimension)) * (2 * radius) ^ exponent :=
          mul_le_mul_of_nonneg_right (coverUpper radius radiusPositive radiusInRange.2)
            (Real.rpow_nonneg (by positivity) _)
        _ = massConstant * (2 : ℝ) ^ exponent * radius ^ (exponent - dimension) := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) radiusPositive.le]
          calc
            (massConstant * radius ^ (-dimension)) * ((2 : ℝ) ^ exponent * radius ^ exponent) =
                massConstant * (2 : ℝ) ^ exponent * (radius ^ (-dimension) * radius ^ exponent) := by ring
            _ = _ := by rw [← Real.rpow_add radiusPositive]; congr 2; ring
    calc
      (∑ center : centers radius, Metric.ediam (coverSets radius center) ^ exponent) ≤
          ∑ _center : centers radius, (2 * ENNReal.ofReal radius) ^ exponent :=
        Finset.sum_le_sum (fun center _ => ENNReal.rpow_le_rpow Metric.ediam_closedEBall_le exponentPositive.le)
      _ = ENNReal.ofReal ((Fintype.card (centers radius) : ℝ) * (2 * radius) ^ exponent) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg (by positivity) exponentPositive.le,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal realCost
  have costLimit : Tendsto (fun radius : ℝ =>
      ∑ center : centers radius, Metric.ediam (coverSets radius center) ^ exponent)
      (𝓝[>] 0) (𝓝 0) := by
    have realLimit : Tendsto (fun radius : ℝ =>
        massConstant * (2 : ℝ) ^ exponent * radius ^ (exponent - dimension)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.zero_rpow (sub_pos.mpr strictExponent).ne', mul_zero] using
        ((((Real.continuousAt_rpow_const (0 : ℝ) (exponent - dimension)
          (Or.inr (sub_pos.mpr strictExponent).le)).tendsto).mono_left nhdsWithin_le_nhds).const_mul
          (massConstant * (2 : ℝ) ^ exponent))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal realLimit)
      (Eventually.of_forall fun _ => zero_le _) costUpper
  have radiusLimit : Tendsto (fun radius : ℝ => 2 * ENNReal.ofReal radius) (𝓝[>] 0) (𝓝 0) := by
    have realIdentityLimit : Tendsto (fun radius : ℝ => radius) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have baseLimit : Tendsto (fun radius : ℝ => ENNReal.ofReal radius) (𝓝[>] 0) (𝓝 0) :=
      by simpa only [ENNReal.ofReal_zero] using
        ENNReal.tendsto_ofReal realIdentityLimit
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := 2) baseLimit
      (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
  have measureBound := Measure.hausdorffMeasure_le_liminf_sum exponent (Set.univ : Set Space)
    (fun radius : ℝ => 2 * ENNReal.ofReal radius) radiusLimit coverSets
    (Eventually.of_forall fun radius center => Metric.ediam_closedEBall_le)
    (show ∀ᶠ radius : ℝ in 𝓝[>] 0, (Set.univ : Set Space) ⊆ ⋃ center : centers radius, coverSets radius center by
      filter_upwards [self_mem_nhdsWithin] with radius radiusPositive
      intro point _
      have finiteCover := compact_coveringNumber_univ_ne_top (Space := Space) (Real.toNNReal radius)
        (Real.toNNReal_pos.mpr radiusPositive)
      obtain ⟨center, centerInCover, near⟩ := Metric.isCover_minimalCover finiteCover (Set.mem_univ point)
      exact Set.mem_iUnion.mpr ⟨⟨center, centerInCover⟩, by
        simpa only [coverSets, Metric.mem_closedEBall, ENNReal.ofReal] using near⟩)
  exact le_antisymm (by simpa only [costLimit.liminf_eq] using measureBound) bot_le

end
end IGS.Sec31

#print axioms IGS.Sec31.hausdorffMeasure_zero_of_coveringNumber_power_upper
