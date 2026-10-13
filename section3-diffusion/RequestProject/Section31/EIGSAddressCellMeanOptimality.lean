import RequestProject.Section31.EIGSAddressCellAverage

/-! Least-square optimality of the actual address-cell means. The averaging
error is compared with every actual cell-constant function by a proved
quadratic identity; no Poincaré or target approximation estimate is assumed. -/

namespace IGS.Sec31

open MeasureTheory
open scoped BigOperators

 theorem integral_square_sub_mean_le
    {Sample : Type*} [MeasurableSpace Sample] (law : Measure Sample) [IsFiniteMeasure law]
    (values : Sample → ℝ) (valuesIntegrable : Integrable values law)
    (squareIntegrable : Integrable (fun sample => values sample ^ 2) law)
    (massPositive : 0 < law.real Set.univ) (constant : ℝ) :
    (∫ sample, (values sample - (∫ sample, values sample ∂law) / law.real Set.univ) ^ 2 ∂law) ≤
      ∫ sample, (values sample - constant) ^ 2 ∂law := by
  have shiftedIntegral (offset : ℝ) :
      (∫ sample, (values sample - offset) ^ 2 ∂law) =
        (∫ sample, values sample ^ 2 ∂law) - 2 * offset * (∫ sample, values sample ∂law) +
          offset ^ 2 * law.real Set.univ := by
    have polynomial : (fun sample => (values sample - offset) ^ 2) =
        (fun sample => values sample ^ 2 - (2 * offset) * values sample + offset ^ 2) := by
      funext sample
      ring
    rw [polynomial, integral_add (squareIntegrable.sub (valuesIntegrable.const_mul (2 * offset)))
      (integrable_const _), integral_sub squareIntegrable (valuesIntegrable.const_mul (2 * offset)),
      integral_const_mul, integral_const]
    simp only [smul_eq_mul]
    ring
  rw [shiftedIntegral, shiftedIntegral]
  have differenceIdentity :
      ((∫ sample, values sample ^ 2 ∂law) - 2 * constant * (∫ sample, values sample ∂law) +
          constant ^ 2 * law.real Set.univ) -
        ((∫ sample, values sample ^ 2 ∂law) -
          2 * ((∫ sample, values sample ∂law) / law.real Set.univ) * (∫ sample, values sample ∂law) +
          ((∫ sample, values sample ∂law) / law.real Set.univ) ^ 2 * law.real Set.univ) =
      law.real Set.univ * (constant - (∫ sample, values sample ∂law) / law.real Set.univ) ^ 2 := by
    field_simp [massPositive.ne']
    <;> ring
  have nonnegative := mul_nonneg massPositive.le
    (sq_nonneg (constant - (∫ sample, values sample ∂law) / law.real Set.univ))
  linarith

 theorem integral_eq_sum_coordinate_fibres
    {Sample Index : Type*} [MeasurableSpace Sample] [Fintype Index]
    [MeasurableSpace Index] [DiscreteMeasurableSpace Index]
    (law : Measure Sample) (coordinate : Sample → Index) (coordinateMeasurable : Measurable coordinate)
    (values : Sample → ℝ) (valuesIntegrable : Integrable values law) :
    (∫ sample, values sample ∂law) =
      ∑ index : Index, ∫ sample in {sample | coordinate sample = index}, values sample ∂law := by
  classical
  have cellMeasurable (index : Index) : MeasurableSet {sample | coordinate sample = index} :=
    coordinateMeasurable (measurableSet_singleton index)
  calc
    _ = ∫ sample, ∑ index : Index, ({sample | coordinate sample = index} : Set Sample).indicator values sample ∂law := by
      congr 1
      funext sample
      simp [Set.indicator, eq_comm]
    _ = ∑ index : Index, ∫ sample, ({sample | coordinate sample = index} : Set Sample).indicator values sample ∂law :=
      integral_finset_sum Finset.univ (fun index _ => valuesIntegrable.indicator (cellMeasurable index))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      exact integral_indicator (cellMeasurable index)

 theorem integrable_square_sub_finite_coordinate
    {Sample Index : Type*} [MeasurableSpace Sample] [Fintype Index]
    [MeasurableSpace Index] [DiscreteMeasurableSpace Index]
    (law : Measure Sample) [IsFiniteMeasure law]
    (coordinate : Sample → Index) (coordinateMeasurable : Measurable coordinate)
    (values : Sample → ℝ) (valuesIntegrable : Integrable values law)
    (squareIntegrable : Integrable (fun sample => values sample ^ 2) law)
    (constants : Index → ℝ) :
    Integrable (fun sample => (values sample - constants (coordinate sample)) ^ 2) law := by
  have constantsMeasurable : Measurable (fun sample => constants (coordinate sample)) :=
    (measurable_of_countable constants).comp coordinateMeasurable
  have constantSquareIntegrable : Integrable (fun sample => constants (coordinate sample) ^ 2) law := by
    apply Integrable.of_bound (constantsMeasurable.pow_const 2).aestronglyMeasurable (‖constants‖ ^ 2)
    exact Filter.Eventually.of_forall fun sample => by
      have bounded := norm_le_pi_norm constants (coordinate sample)
      simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
        (pow_le_pow_left₀ (norm_nonneg _) bounded 2)
  apply Integrable.mono' ((squareIntegrable.const_mul 2).add (constantSquareIntegrable.const_mul 2))
    ((valuesIntegrable.aestronglyMeasurable.sub constantsMeasurable.aestronglyMeasurable).pow 2)
  exact Filter.Eventually.of_forall fun sample => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (values sample + constants (coordinate sample))]

end IGS.Sec31

namespace EIGS

open IGS.Sec31 MeasureTheory
open scoped BigOperators Classical ENNReal
noncomputable section
set_option maxHeartbeats 3000000
variable {K : ℕ}

theorem xiAddressCellAverage_minimizes_square_error
    (system : EIGSData K) (mass : XiMassParameters system) (level : ℕ)
    (values : XiEdgeAddress system → ℝ) (valuesIntegrable : Integrable values mass.addressMeasure)
    (squareIntegrable : Integrable (fun address => values address ^ 2) mass.addressMeasure)
    (constants : XiEdge system.toRuleData level → ℝ) :
    (∫ address, (values address - xiAddressCellAverage system mass level values address) ^ 2 ∂mass.addressMeasure) ≤
      ∫ address, (values address - constants (xiAddressEdge system level address)) ^ 2 ∂mass.addressMeasure := by
  have coordinateMeasurable := measurable_xiAddressEdge system level
  have cellMeasurable (edge : XiEdge system.toRuleData level) :
      MeasurableSet {address | xiAddressEdge system level address = edge} :=
    coordinateMeasurable (measurableSet_singleton edge)
  have fibreIntegral (coefficients : XiEdge system.toRuleData level → ℝ) (edge : XiEdge system.toRuleData level) :
      (∫ address in {address | xiAddressEdge system level address = edge},
        (values address - coefficients (xiAddressEdge system level address)) ^ 2 ∂mass.addressMeasure) =
      (∫ address in {address | xiAddressEdge system level address = edge},
        (values address - coefficients edge) ^ 2 ∂mass.addressMeasure) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (cellMeasurable edge)] with address membership
    simp only [Set.mem_setOf_eq] at membership
    rw [membership]
  rw [integral_eq_sum_coordinate_fibres mass.addressMeasure (xiAddressEdge system level) coordinateMeasurable _
    (integrable_square_sub_finite_coordinate mass.addressMeasure (xiAddressEdge system level) coordinateMeasurable
      values valuesIntegrable squareIntegrable (xiAddressCellMean system mass level values)),
    integral_eq_sum_coordinate_fibres mass.addressMeasure (xiAddressEdge system level) coordinateMeasurable _
    (integrable_square_sub_finite_coordinate mass.addressMeasure (xiAddressEdge system level) coordinateMeasurable
      values valuesIntegrable squareIntegrable constants)]
  apply Finset.sum_le_sum
  intro edge _
  change (∫ address in {address | xiAddressEdge system level address = edge},
      (values address - xiAddressCellMean system mass level values (xiAddressEdge system level address)) ^ 2
      ∂mass.addressMeasure) ≤ _
  rw [fibreIntegral, fibreIntegral]
  have cellMass : (mass.addressMeasure.restrict {address | xiAddressEdge system level address = edge}).real Set.univ =
      mass.edgeWeight level edge := by
    simp only [measureReal_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rw [mass.addressMeasure_cylinder]
    exact ENNReal.toReal_ofReal (mass.edgeWeight_positive level edge).le
  have massPositive : 0 < (mass.addressMeasure.restrict
      {address | xiAddressEdge system level address = edge}).real Set.univ := by
    rw [cellMass]
    exact mass.edgeWeight_positive level edge
  have minimality := integral_square_sub_mean_le
    (mass.addressMeasure.restrict {address | xiAddressEdge system level address = edge})
    values valuesIntegrable.restrict squareIntegrable.restrict massPositive (constants edge)
  simpa only [cellMass, xiAddressCellMean] using minimality

end
end EIGS

#print axioms IGS.Sec31.integral_square_sub_mean_le
#print axioms IGS.Sec31.integral_eq_sum_coordinate_fibres
#print axioms IGS.Sec31.integrable_square_sub_finite_coordinate
#print axioms EIGS.xiAddressCellAverage_minimizes_square_error
