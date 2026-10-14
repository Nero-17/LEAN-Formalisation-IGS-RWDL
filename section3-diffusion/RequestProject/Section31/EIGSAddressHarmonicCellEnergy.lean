import RequestProject.Section31.EIGSAddressCellMeanOptimality
import RequestProject.Section31.EIGSContinuousProjectionTail
import RequestProject.Section31.EIGSCellOscillation

/-! Harmonic values at the actual address limit remain in their coarse-cell
endpoint interval. The actual cylinder weights turn the squared endpoint
oscillations into the native trace energy with the mass-resistance scale.
No restriction that the resistance rate exceed one is used. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 3000000
variable {K : ℕ}

theorem xiAddressEdge_ancestor (system : EIGSData K) (level offset : ℕ) (address : XiEdgeAddress system) :
    xiAncestorEdge system level offset (xiAddressEdge system (level + offset) address) =
      xiAddressEdge system level address := by
  induction offset with
  | zero => rfl
  | succ offset induction =>
      change xiAncestorEdge system level offset
        (xiEdgeParent system (level + offset) (xiAddressEdge system ((level + offset) + 1) address)) = _
      rw [xiAddressEdge_parent]
      exact induction

theorem xiContinuousHarmonic_address_endpoint_range
    (system : EIGSData K) (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (level : ℕ) (values : XiVtx system level → ℝ)
    (extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair, ℝ))
    (extensionAgreement : ∀ vertex,
      extension (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair vertex) =
      xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair level values vertex)
    (address : XiEdgeAddress system) :
    min (values (XiTail system level (xiAddressEdge system level address)))
        (values (XiHead system level (xiAddressEdge system level address))) ≤
      extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair address) ∧
    extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair address) ≤
      max (values (XiTail system level (xiAddressEdge system level address)))
        (values (XiHead system level (xiAddressEdge system level address))) := by
  have shifted : Tendsto (fun offset : ℕ => level + offset) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat level
  have pointLimit := (xiAddressTailApproximation_tendsto system rulesConnected lengths lengthsPositive distanceRate
    distanceGreaterThanOne metricEigenpair address).comp shifted
  have valueLimit : Tendsto (fun offset => extension (xiAddressTailApproximation system rulesConnected lengths lengthsPositive
      distanceRate distanceGreaterThanOne metricEigenpair (level + offset) address)) atTop
      (nhds (extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair address))) := by
    simpa only [Function.comp_apply] using extension.continuous.continuousAt.tendsto.comp pointLimit
  have ranges (offset : ℕ) :
      min (values (XiTail system level (xiAddressEdge system level address)))
          (values (XiHead system level (xiAddressEdge system level address))) ≤
        extension (xiAddressTailApproximation system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne
          metricEigenpair (level + offset) address) ∧
      extension (xiAddressTailApproximation system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne
          metricEigenpair (level + offset) address) ≤
        max (values (XiTail system level (xiAddressEdge system level address)))
          (values (XiHead system level (xiAddressEdge system level address))) := by
    have range := (xiHarmonicValues_descendant_endpoint_range system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair level values offset
      (xiAddressEdge system (level + offset) address)).1
    have agreement := (extensionAgreement (xiVertexEmbedding system (level + offset)
      (XiTail system (level + offset) (xiAddressEdge system (level + offset) address)))).trans
      (xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair level values offset _)
    change extension (xiAddressTailApproximation system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne
      metricEigenpair (level + offset) address) = _ at agreement
    rw [xiAddressEdge_ancestor] at range
    rw [agreement]
    exact range
  exact ⟨ge_of_tendsto valueLimit (Filter.Eventually.of_forall fun offset => (ranges offset).1),
    le_of_tendsto valueLimit (Filter.Eventually.of_forall fun offset => (ranges offset).2)⟩

theorem square_distance_to_endpoint_le (first second value : ℝ)
    (valueLower : min first second ≤ value) (valueUpper : value ≤ max first second) :
    (value - first) ^ 2 ≤ (second - first) ^ 2 := by
  rcases le_total first second with ordered | ordered
  · rw [min_eq_left ordered] at valueLower
    rw [max_eq_right ordered] at valueUpper
    exact (sq_le_sq₀ (sub_nonneg.mpr valueLower) (sub_nonneg.mpr ordered)).2 (sub_le_sub_right valueUpper first)
  · rw [min_eq_right ordered] at valueLower
    rw [max_eq_left ordered] at valueUpper
    have bound := (sq_le_sq₀ (sub_nonneg.mpr valueUpper) (sub_nonneg.mpr ordered)).2
      (sub_le_sub_left valueLower first)
    simpa only [← neg_sub first value, ← neg_sub first second, neg_sq] using bound

theorem exists_xiCylinder_endpoint_square_energy_bound
    (system : EIGSData K) (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ level (values : XiVtx system level → ℝ),
      (∑ edge : XiEdge system.toRuleData level, mass.edgeWeight level edge *
        (values (XiHead system level edge) - values (XiTail system level edge)) ^ 2) ≤
      constant / (mass.rate * resistanceRate) ^ level *
        (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy values := by
  have amplitudePositive := mass.amplitude_positive
  have massRatePositive := mass.rate_positive
  let constant := (∑ colour : Fin K, mass.amplitude colour * resistanceVector colour) /
    mass.amplitude system.initCol
  have sumPositive : 0 < ∑ colour : Fin K, mass.amplitude colour * resistanceVector colour :=
    (mul_pos (amplitudePositive system.initCol) (vectorPositive system.initCol)).trans_le
      (Finset.single_le_sum (fun colour _ => (mul_pos (amplitudePositive colour) (vectorPositive colour)).le)
        (Finset.mem_univ system.initCol))
  refine ⟨constant, div_pos sumPositive (amplitudePositive _), ?_⟩
  intro level values
  rw [xiWeightedFiniteNetwork_energy_eq_potential]
  change (∑ edge : XiEdge system.toRuleData level, mass.edgeWeight level edge *
      (values (XiHead system level edge) - values (XiTail system level edge)) ^ 2) ≤
    constant / (mass.rate * resistanceRate) ^ level *
      (resistanceRate ^ level * ∑ edge : XiEdge system.toRuleData level,
        (resistanceVector (XiCol system.toRuleData level edge))⁻¹ *
          (values (XiTail system level edge) - values (XiHead system level edge)) ^ 2)
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro edge _
  have colourBound : mass.amplitude (XiCol system.toRuleData level edge) *
      resistanceVector (XiCol system.toRuleData level edge) ≤
      ∑ colour : Fin K, mass.amplitude colour * resistanceVector colour :=
    Finset.single_le_sum (fun colour _ => (mul_pos (amplitudePositive colour) (vectorPositive colour)).le)
      (Finset.mem_univ _)
  have coefficientBound : mass.edgeWeight level edge ≤
      constant / (mass.rate * resistanceRate) ^ level * resistanceRate ^ level *
        (resistanceVector (XiCol system.toRuleData level edge))⁻¹ := by
    dsimp only [XiMassParameters.edgeWeight, constant]
    rw [mul_pow]
    apply (div_le_iff₀ (mul_pos (pow_pos mass.rate_positive level) (amplitudePositive _))).mpr
    have denominatorIdentity :
        ((∑ colour : Fin K, mass.amplitude colour * resistanceVector colour) /
            mass.amplitude system.initCol /
          (mass.rate ^ level * resistanceRate ^ level) * resistanceRate ^ level *
          (resistanceVector (XiCol system.toRuleData level edge))⁻¹) *
          (mass.rate ^ level * mass.amplitude system.initCol) =
        (∑ colour : Fin K, mass.amplitude colour * resistanceVector colour) /
          resistanceVector (XiCol system.toRuleData level edge) := by
      field_simp [(amplitudePositive system.initCol).ne', (pow_pos mass.rate_positive level).ne',
        (pow_pos ratePositive level).ne', (vectorPositive (XiCol system.toRuleData level edge)).ne']
      <;> ring
    rw [denominatorIdentity]
    exact (le_div_iff₀ (vectorPositive _)).mpr colourBound
  have multiplied := mul_le_mul_of_nonneg_right coefficientBound
    (sq_nonneg (values (XiHead system level edge) - values (XiTail system level edge)))
  have squareIdentity : (values (XiTail system level edge) - values (XiHead system level edge)) ^ 2 =
      (values (XiHead system level edge) - values (XiTail system level edge)) ^ 2 := by ring
  simpa only [← mul_assoc, squareIdentity] using multiplied

theorem xiAddress_coordinate_integral (system : EIGSData K) (mass : XiMassParameters system)
    (level : ℕ) (values : XiEdge system.toRuleData level → ℝ) :
    (∫ address, values (xiAddressEdge system level address) ∂mass.addressMeasure) =
      ∑ edge : XiEdge system.toRuleData level, mass.edgeWeight level edge * values edge := by
  have mapped := integral_map (μ := mass.addressMeasure) (measurable_xiAddressEdge system level).aemeasurable
    (measurable_of_countable values).aestronglyMeasurable
  rw [mass.addressMeasure_coordinate] at mapped
  rw [← mapped, integral_fintype _ Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro edge _
  have singletonLaw := (mass.edgePMF level).toMeasure_apply_singleton edge (measurableSet_singleton edge)
  change mass.edgeLaw level {edge} = ENNReal.ofReal (mass.edgeWeight level edge) at singletonLaw
  rw [measureReal_def, singletonLaw, ENNReal.toReal_ofReal (mass.edgeWeight_positive level edge).le]
  simp only [smul_eq_mul]

theorem xiContinuous_address_integrable
    (system : EIGSData K) (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair, ℝ)) :
    Integrable (fun address => target (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair address)) mass.addressMeasure ∧
    Integrable (fun address => target (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair address) ^ 2) mass.addressMeasure := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceGreaterThanOne metricEigenpair
  have targetMeasurable := target.continuous.measurable.comp
    (measurable_xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair)
  constructor
  · apply Integrable.of_bound targetMeasurable.aestronglyMeasurable ‖target‖
    exact Filter.Eventually.of_forall fun address => target.norm_coe_le_norm _
  · apply Integrable.of_bound (targetMeasurable.pow_const 2).aestronglyMeasurable (‖target‖ ^ 2)
    exact Filter.Eventually.of_forall fun address => by
      simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
        pow_le_pow_left₀ (norm_nonneg _) (target.norm_coe_le_norm
          (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair address)) 2

theorem xiContinuousHarmonic_address_tail_square_bound
    (system : EIGSData K) (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (level : ℕ) (values : XiVtx system level → ℝ)
    (extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair, ℝ))
    (extensionAgreement : ∀ vertex,
      extension (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair vertex) =
      xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair level values vertex) :
    (∫ address, (extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair address) - values (XiTail system level (xiAddressEdge system level address))) ^ 2
      ∂mass.addressMeasure) ≤
    ∑ edge : XiEdge system.toRuleData level, mass.edgeWeight level edge *
      (values (XiHead system level edge) - values (XiTail system level edge)) ^ 2 := by
  obtain ⟨extensionIntegrable, extensionSquareIntegrable⟩ := xiContinuous_address_integrable system rulesConnected
    lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair mass extension
  have differenceIntegrable := integrable_square_sub_finite_coordinate mass.addressMeasure
    (xiAddressEdge system level) (measurable_xiAddressEdge system level)
    _ extensionIntegrable extensionSquareIntegrable (fun edge => values (XiTail system level edge))
  have upperIntegrable : Integrable (fun address =>
      (values (XiHead system level (xiAddressEdge system level address)) -
        values (XiTail system level (xiAddressEdge system level address))) ^ 2) mass.addressMeasure := by
    exact (show Integrable (fun edge : XiEdge system.toRuleData level =>
      (values (XiHead system level edge) - values (XiTail system level edge)) ^ 2)
      (mass.addressMeasure.map (xiAddressEdge system level)) from Integrable.of_finite).comp_measurable
        (measurable_xiAddressEdge system level)
  have integralBound := integral_mono differenceIntegrable upperIntegrable (fun address =>
    square_distance_to_endpoint_le _ _ _
      (xiContinuousHarmonic_address_endpoint_range system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair level values extension extensionAgreement address).1
      (xiContinuousHarmonic_address_endpoint_range system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair level values extension extensionAgreement address).2)
  exact integralBound.trans_eq (xiAddress_coordinate_integral system mass level
    (fun edge => (values (XiHead system level edge) - values (XiTail system level edge)) ^ 2))

end
end EIGS

#print axioms EIGS.xiAddressEdge_ancestor
#print axioms EIGS.xiContinuousHarmonic_address_endpoint_range
#print axioms EIGS.square_distance_to_endpoint_le
#print axioms EIGS.exists_xiCylinder_endpoint_square_energy_bound

#print axioms EIGS.xiAddress_coordinate_integral
#print axioms EIGS.xiContinuous_address_integrable
#print axioms EIGS.xiContinuousHarmonic_address_tail_square_bound
