import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual bounded finite-rank averaging maps on an L² finite partition.
The definition uses indicator vectors and integral functionals, so it acts
on L² classes and has no representative-choice or quotient-boundary premise. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal
noncomputable section

theorem L2_norm_sq_eq_integral_square {Sample : Type*} [MeasurableSpace Sample]
    (law : Measure Sample) (values : Lp ℝ 2 law) :
    ‖values‖ ^ 2 = ∫ sample, values sample ^ 2 ∂law := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem isCompactOperator_of_proper_domain
    {Input Output : Type*} [NormedAddCommGroup Input] [NormedSpace ℝ Input]
    [ProperSpace Input] [NormedAddCommGroup Output] [NormedSpace ℝ Output]
    (operator : Input →L[ℝ] Output) : IsCompactOperator operator := by
  apply (isCompactOperator_iff_image_closedBall_subset_compact operator.toLinearMap zero_lt_one).mpr
  exact ⟨operator '' Metric.closedBall 0 1,
    (isCompact_closedBall (0 : Input) 1).image operator.continuous, Set.Subset.rfl⟩

theorem isCompactOperator_smulRight
    {Input Output : Type*} [NormedAddCommGroup Input] [NormedSpace ℝ Input]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output]
    (functional : StrongDual ℝ Input) (vector : Output) :
    IsCompactOperator (functional.smulRight vector) := by
  let scalarMap : ℝ →L[ℝ] Output := (ContinuousLinearMap.id ℝ ℝ).smulRight vector
  have compact := (isCompactOperator_of_proper_domain scalarMap).comp_clm functional
  convert compact using 1

variable {Sample Index : Type*} [MeasurableSpace Sample] [Fintype Index]
    [MeasurableSpace Index] [DiscreteMeasurableSpace Index]
    (law : Measure Sample) [IsFiniteMeasure law]
    (coordinate : Sample → Index) (coordinateMeasurable : Measurable coordinate)

def finitePartitionL2Indicator (index : Index) : Lp ℝ 2 law :=
  indicatorConstLp 2 (coordinateMeasurable (measurableSet_singleton index)) (measure_ne_top law _) (1 : ℝ)

def finitePartitionL2Average (weights : Index → ℝ) : Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law :=
  ∑ index : Index, (weights index)⁻¹ •
    (innerSL ℝ (finitePartitionL2Indicator law coordinate coordinateMeasurable index)).smulRight
      (finitePartitionL2Indicator law coordinate coordinateMeasurable index)

theorem finitePartitionL2Average_compact (weights : Index → ℝ) :
    IsCompactOperator (finitePartitionL2Average law coordinate coordinateMeasurable weights) := by
  classical
  unfold finitePartitionL2Average
  induction (Finset.univ : Finset Index) using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (isCompactOperator_zero (M₁ := Lp ℝ 2 law) (M₂ := Lp ℝ 2 law))
  | @insert index remaining indexNotMem induction =>
      rw [Finset.sum_insert indexNotMem]
      exact ((isCompactOperator_smulRight _ _).smul _).add induction

theorem L2_coeFn_finset_sum_ae (indices : Finset Index) (vectors : Index → Lp ℝ 2 law) :
    (fun sample => (∑ index ∈ indices, vectors index) sample) =ᵐ[law]
      (fun sample => ∑ index ∈ indices, vectors index sample) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero ℝ 2 law)
  | @insert index remaining indexNotMem induction =>
      simp only [Finset.sum_insert indexNotMem]
      filter_upwards [Lp.coeFn_add (vectors index) (∑ other ∈ remaining, vectors other), induction]
        with sample addition sumEquality
      change (vectors index + ∑ other ∈ remaining, vectors other) sample = _ at addition ⊢
      rw [addition]
      change vectors index sample + (∑ other ∈ remaining, vectors other) sample = _
      rw [sumEquality]

theorem finitePartitionL2Average_ae (weights : Index → ℝ) (values : Lp ℝ 2 law) :
    (fun sample => finitePartitionL2Average law coordinate coordinateMeasurable weights values sample) =ᵐ[law]
      (fun sample =>
        (∫ other in {other | coordinate other = coordinate sample}, values other ∂law) / weights (coordinate sample)) := by
  classical
  let vectors : Index → Lp ℝ 2 law := fun index =>
    ((weights index)⁻¹ * inner ℝ (finitePartitionL2Indicator law coordinate coordinateMeasurable index) values) •
      finitePartitionL2Indicator law coordinate coordinateMeasurable index
  have vectorAE (index : Index) :
      (fun sample => vectors index sample) =ᵐ[law]
        (fun sample => ((∫ other in {other | coordinate other = index}, values other ∂law) / weights index) *
          ({other | coordinate other = index} : Set Sample).indicator (fun _ => (1 : ℝ)) sample) := by
    filter_upwards [Lp.coeFn_smul
      ((weights index)⁻¹ * inner ℝ (finitePartitionL2Indicator law coordinate coordinateMeasurable index) values)
      (finitePartitionL2Indicator law coordinate coordinateMeasurable index),
      indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
        (hs := coordinateMeasurable (measurableSet_singleton index))
        (hμs := measure_ne_top law _) (c := (1 : ℝ))] with sample scaling indicator
    change vectors index sample = _ at scaling ⊢
    rw [scaling]
    change _ * finitePartitionL2Indicator law coordinate coordinateMeasurable index sample = _
    change finitePartitionL2Indicator law coordinate coordinateMeasurable index sample =
      ({other | coordinate other = index} : Set Sample).indicator (fun _ => (1 : ℝ)) sample at indicator
    rw [indicator]
    simp only [finitePartitionL2Indicator, L2.inner_indicatorConstLp_one, div_eq_mul_inv,
      mul_comm]
    rfl
  have averageEquality : finitePartitionL2Average law coordinate coordinateMeasurable weights values =
      ∑ index : Index, vectors index := by
    simp only [finitePartitionL2Average, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, vectors, smul_smul]
  rw [averageEquality]
  filter_upwards [L2_coeFn_finset_sum_ae law Finset.univ vectors, ae_all_iff.mpr vectorAE]
    with sample sumEquality termsEquality
  rw [sumEquality]
  simp only [termsEquality]
  simp [Set.indicator, eq_comm]

end
end IGS.Sec31

#print axioms IGS.Sec31.isCompactOperator_of_proper_domain
#print axioms IGS.Sec31.L2_norm_sq_eq_integral_square
#print axioms IGS.Sec31.isCompactOperator_smulRight
#print axioms IGS.Sec31.finitePartitionL2Average_compact
#print axioms IGS.Sec31.finitePartitionL2Average_ae
