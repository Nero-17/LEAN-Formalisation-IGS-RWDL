import RequestProject.Section31.EIGSAddressMeasure
import RequestProject.Section31.EIGSMetricOfRules
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Actual conditional cell means on the finite address partition. Cylinder
masses are the already proved positive Perron weights. Their lower bound
and exact marginal law give a genuine L¹-to-L² estimate for this finite-rank
averaging operator. The energy estimate for the averaging error remains a
separate obligation; it is not an input to the original-rule mean bound. -/

namespace IGS.Sec31

open MeasureTheory
open scoped BigOperators

 theorem finite_partition_integral_abs_sum_le
    {Sample Index : Type*} [MeasurableSpace Sample] [Fintype Index]
    [MeasurableSpace Index] [DiscreteMeasurableSpace Index]
    (law : Measure Sample) (coordinate : Sample → Index) (coordinateMeasurable : Measurable coordinate)
    (values : Sample → ℝ) (valuesIntegrable : Integrable values law) :
    (∑ index : Index, |∫ sample in {sample | coordinate sample = index}, values sample ∂law|) ≤
      ∫ sample, |values sample| ∂law := by
  classical
  have cellMeasurable (index : Index) : MeasurableSet {sample | coordinate sample = index} :=
    coordinateMeasurable (measurableSet_singleton index)
  calc
    _ ≤ ∑ index : Index, ∫ sample in {sample | coordinate sample = index}, |values sample| ∂law :=
      Finset.sum_le_sum (fun index _ => abs_integral_le_integral_abs)
    _ = ∑ index : Index, ∫ sample, ({sample | coordinate sample = index} : Set Sample).indicator
        (fun sample => |values sample|) sample ∂law := by
      apply Finset.sum_congr rfl
      intro index _
      exact (integral_indicator (cellMeasurable index)).symm
    _ = ∫ sample, ∑ index : Index, ({sample | coordinate sample = index} : Set Sample).indicator
        (fun sample => |values sample|) sample ∂law :=
      (integral_finset_sum Finset.univ (fun index _ => valuesIntegrable.abs.indicator (cellMeasurable index))).symm
    _ = ∫ sample, |values sample| ∂law := by
      congr 1
      funext sample
      simp only [Set.indicator, Set.mem_setOf_eq]
      simp [eq_comm]

 theorem weighted_cell_mean_square_le
    {Index : Type*} [Fintype Index]
    (weights amounts : Index → ℝ) (lower : ℝ) (lowerPositive : 0 < lower)
    (weightsLower : ∀ index, lower ≤ weights index) :
    (∑ index : Index, weights index * (amounts index / weights index) ^ 2) ≤
      (∑ index : Index, |amounts index|) ^ 2 / lower := by
  classical
  have weightsPositive (index : Index) : 0 < weights index := lowerPositive.trans_le (weightsLower index)
  calc
    _ = ∑ index : Index, amounts index ^ 2 / weights index := by
      apply Finset.sum_congr rfl
      intro index _
      field_simp [(weightsPositive index).ne']
      <;> ring
    _ ≤ ∑ index : Index, amounts index ^ 2 / lower :=
      Finset.sum_le_sum (fun index _ =>
        div_le_div_of_nonneg_left (sq_nonneg _) lowerPositive (weightsLower index))
    _ = (∑ index : Index, amounts index ^ 2) / lower := by rw [Finset.sum_div]
    _ ≤ (∑ index : Index, |amounts index|) ^ 2 / lower := by
      apply div_le_div_of_nonneg_right _ lowerPositive.le
      simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset Index)) (f := fun index => |amounts index|)
        (fun index _ => abs_nonneg (amounts index))

end IGS.Sec31

namespace EIGS

open IGS.Sec31 MeasureTheory
open scoped BigOperators Classical ENNReal
noncomputable section
set_option maxHeartbeats 3000000
variable {K : ℕ}

def xiAddressCellMean (system : EIGSData K) (mass : XiMassParameters system)
    (level : ℕ) (values : XiEdgeAddress system → ℝ) (edge : XiEdge system.toRuleData level) : ℝ :=
  (∫ address in {address | xiAddressEdge system level address = edge}, values address ∂mass.addressMeasure) /
    mass.edgeWeight level edge

def xiAddressCellAverage (system : EIGSData K) (mass : XiMassParameters system)
    (level : ℕ) (values : XiEdgeAddress system → ℝ) (address : XiEdgeAddress system) : ℝ :=
  xiAddressCellMean system mass level values (xiAddressEdge system level address)

theorem xiAddressCellAverage_square_integral
    (system : EIGSData K) (mass : XiMassParameters system) (level : ℕ)
    (values : XiEdgeAddress system → ℝ) :
    (∫ address, xiAddressCellAverage system mass level values address ^ 2 ∂mass.addressMeasure) =
      ∑ edge : XiEdge system.toRuleData level,
        mass.edgeWeight level edge * xiAddressCellMean system mass level values edge ^ 2 := by
  have mapped := integral_map (measurable_xiAddressEdge system level).aemeasurable
    (measurable_of_countable (fun edge : XiEdge system.toRuleData level =>
      xiAddressCellMean system mass level values edge ^ 2)).aestronglyMeasurable
  rw [mass.addressMeasure_coordinate] at mapped
  change (∫ edge, xiAddressCellMean system mass level values edge ^ 2 ∂mass.edgeLaw level) =
    (∫ address, xiAddressCellAverage system mass level values address ^ 2 ∂mass.addressMeasure) at mapped
  rw [← mapped, integral_fintype _ Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro edge _
  have singletonLaw := (mass.edgePMF level).toMeasure_apply_singleton edge (measurableSet_singleton edge)
  change mass.edgeLaw level {edge} = ENNReal.ofReal (mass.edgeWeight level edge) at singletonLaw
  rw [measureReal_def, singletonLaw, ENNReal.toReal_ofReal (mass.edgeWeight_positive level edge).le]
  simp only [smul_eq_mul]

theorem exists_xiAddressCellAverage_L1_L2_bound
    (system : EIGSData K) (mass : XiMassParameters system) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ level (values : XiEdgeAddress system → ℝ),
      Integrable values mass.addressMeasure →
      (∫ address, xiAddressCellAverage system mass level values address ^ 2 ∂mass.addressMeasure) ≤
        constant * mass.rate ^ level * (∫ address, |values address| ∂mass.addressMeasure) ^ 2 := by
  have amplitudePositive := mass.amplitude_positive
  have ratePositive := mass.rate_positive
  obtain ⟨minimumColour, _, minimumCondition⟩ := Finset.exists_min_image
    Finset.univ mass.amplitude ⟨system.initCol, Finset.mem_univ _⟩
  refine ⟨mass.amplitude system.initCol / mass.amplitude minimumColour, by positivity, ?_⟩
  intro level values valuesIntegrable
  have lowerPositive : 0 < mass.amplitude minimumColour /
      (mass.rate ^ level * mass.amplitude system.initCol) := by
    have ratePositive := mass.rate_positive
    have amplitudePositive := mass.amplitude_positive
    positivity
  have weightsLower (edge : XiEdge system.toRuleData level) :
      mass.amplitude minimumColour / (mass.rate ^ level * mass.amplitude system.initCol) ≤
        mass.edgeWeight level edge := by
    apply div_le_div_of_nonneg_right (minimumCondition _ (Finset.mem_univ _))
    exact (mul_pos (pow_pos mass.rate_positive level) (mass.amplitude_positive _)).le
  rw [xiAddressCellAverage_square_integral]
  have coefficientBound := weighted_cell_mean_square_le (mass.edgeWeight level)
    (fun edge => ∫ address in {address | xiAddressEdge system level address = edge}, values address ∂mass.addressMeasure)
    (mass.amplitude minimumColour / (mass.rate ^ level * mass.amplitude system.initCol)) lowerPositive weightsLower
  have integralBound := finite_partition_integral_abs_sum_le mass.addressMeasure (xiAddressEdge system level)
    (measurable_xiAddressEdge system level) values valuesIntegrable
  have integralNonnegative : 0 ≤ ∫ address, |values address| ∂mass.addressMeasure :=
    integral_nonneg (fun _ => abs_nonneg _)
  have sumNonnegative : 0 ≤ ∑ edge : XiEdge system.toRuleData level,
      |∫ address in {address | xiAddressEdge system level address = edge}, values address ∂mass.addressMeasure| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have squareBound := (sq_le_sq₀ sumNonnegative integralNonnegative).2 integralBound
  have comparison := coefficientBound.trans (div_le_div_of_nonneg_right squareBound lowerPositive.le)
  have coefficientIdentity :
      (∫ address, |values address| ∂mass.addressMeasure) ^ 2 /
        (mass.amplitude minimumColour / (mass.rate ^ level * mass.amplitude system.initCol)) =
      (mass.amplitude system.initCol / mass.amplitude minimumColour) * mass.rate ^ level *
        (∫ address, |values address| ∂mass.addressMeasure) ^ 2 := by
    field_simp [(mass.amplitude_positive minimumColour).ne',
      (mass.amplitude_positive system.initCol).ne', (pow_pos mass.rate_positive level).ne']
    <;> ring
  simpa only [xiAddressCellMean, coefficientIdentity] using comparison

 theorem exists_xiAddressCellAverage_L1_L2_bound_of_rules
    (system : EIGSData K) (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    ∃ constant : ℝ, 0 < constant ∧ ∀ level (values : XiEdgeAddress system → ℝ),
      Integrable values mass.addressMeasure →
      (∫ address, xiAddressCellAverage system mass level values address ^ 2 ∂mass.addressMeasure) ≤
        constant * mass.rate ^ level * (∫ address, |values address| ∂mass.addressMeasure) ^ 2 := by
  exact exists_xiAddressCellAverage_L1_L2_bound system
    (xiMassParametersOfRules system rulesConnected distancePositive)

theorem exists_xiLimitAddressCellAverage_L1_L2_bound
    (system : EIGSData K) (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ level
      (values : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair → ℝ),
      Integrable values (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair mass) →
      (∫ address, xiAddressCellAverage system mass level
        (values ∘ xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair)
        address ^ 2 ∂mass.addressMeasure) ≤ constant * mass.rate ^ level *
        (∫ point, |values point| ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceGreaterThanOne metricEigenpair mass) ^ 2 := by
  obtain ⟨constant, constantPositive, bound⟩ := exists_xiAddressCellAverage_L1_L2_bound system mass
  refine ⟨constant, constantPositive, ?_⟩
  intro level values valuesIntegrable
  have addressMeasurable := measurable_xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
    distanceGreaterThanOne metricEigenpair
  have pulledIntegrable := valuesIntegrable.comp_measurable addressMeasurable
  have comparison := bound level _ pulledIntegrable
  have mapped := integral_map addressMeasurable.aemeasurable valuesIntegrable.abs.aestronglyMeasurable
  change (∫ point, |values point| ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair mass) =
    (∫ address, |values (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair address)| ∂mass.addressMeasure) at mapped
  simpa only [Function.comp_apply, ← mapped] using comparison

 theorem exists_xiLimitAddressCellAverage_L1_L2_bound_of_rules
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    ∃ constant : ℝ, 0 < constant ∧ ∀ level (values : parameters.LimitSpace → ℝ),
      Integrable values (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) →
      (∫ address, xiAddressCellAverage system mass level
        (values ∘ xiAddressLimit system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair) address ^ 2
        ∂mass.addressMeasure) ≤ constant * mass.rate ^ level *
        (∫ point, |values point| ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) ^ 2 := by
  dsimp only
  exact exists_xiLimitAddressCellAverage_L1_L2_bound system rulesConnected _ _ _ _ _ _

end
end EIGS

#print axioms IGS.Sec31.finite_partition_integral_abs_sum_le
#print axioms IGS.Sec31.weighted_cell_mean_square_le
#print axioms EIGS.xiAddressCellAverage_square_integral
#print axioms EIGS.exists_xiAddressCellAverage_L1_L2_bound
#print axioms EIGS.exists_xiAddressCellAverage_L1_L2_bound_of_rules

#print axioms EIGS.exists_xiLimitAddressCellAverage_L1_L2_bound
#print axioms EIGS.exists_xiLimitAddressCellAverage_L1_L2_bound_of_rules
