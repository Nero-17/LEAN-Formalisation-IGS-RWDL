import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! A positive L² operator with strictly positive quadratic pairings cannot
remove any part of the support of a nonnegative input. The proof restricts the
input to the zero set of the output. The semigroup consumer will obtain strict
quadratic pairings from symmetry, the semigroup law, and continuity at zero.
No positivity improvement or irreducibility is assumed.
Candidate source, awaiting whole-file compilation. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Space : Type*} [MeasurableSpace Space] (law : Measure Space)

theorem L2_inner_nonnegative_of_ae_nonnegative (first second : Lp ℝ 2 law)
    (firstNonnegative : ∀ᵐ point ∂law, 0 ≤ first point)
    (secondNonnegative : ∀ᵐ point ∂law, 0 ≤ second point) :
    0 ≤ inner ℝ first second := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [firstNonnegative, secondNonnegative] with point firstBound secondBound
  simpa only [RCLike.inner_apply, conj_trivial] using mul_nonneg secondBound firstBound

theorem L2_inner_eq_zero_iff_product_ae_zero (first second : Lp ℝ 2 law)
    (firstNonnegative : ∀ᵐ point ∂law, 0 ≤ first point)
    (secondNonnegative : ∀ᵐ point ∂law, 0 ≤ second point) :
    inner ℝ first second = 0 ↔ ∀ᵐ point ∂law, first point * second point = 0 := by
  have productNonnegative : ∀ᵐ point ∂law, 0 ≤ inner ℝ (first point) (second point) := by
    filter_upwards [firstNonnegative, secondNonnegative] with point firstBound secondBound
    simpa only [RCLike.inner_apply, conj_trivial] using mul_nonneg secondBound firstBound
  rw [L2.inner_def]
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm, Filter.EventuallyEq, Pi.zero_apply] using
    integral_eq_zero_iff_of_nonneg_ae productNonnegative (L2.integrable_inner (𝕜 := ℝ) first second)

theorem positive_L2_operator_zero_set_inclusion
    (operator : Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law)
    (positive : ∀ values : Lp ℝ 2 law,
      (∀ᵐ point ∂law, 0 ≤ values point) → ∀ᵐ point ∂law, 0 ≤ operator values point)
    (strictPairing : ∀ values : Lp ℝ 2 law, values ≠ 0 → 0 < inner ℝ values (operator values))
    (values : Lp ℝ 2 law) (valuesNonnegative : ∀ᵐ point ∂law, 0 ≤ values point) :
    ∀ᵐ point ∂law, operator values point = 0 → values point = 0 := by
  classical
  let zeroSet : Set Space := {point | operator values point = 0}
  have zeroSetMeasurable : MeasurableSet zeroSet :=
    measurableSet_eq_fun (Lp.stronglyMeasurable (operator values)).measurable measurable_const
  have restrictedMem : MemLp (zeroSet.indicator (fun point => values point)) 2 law :=
    (Lp.memLp values).indicator zeroSetMeasurable
  let restricted : Lp ℝ 2 law := restrictedMem.toLp (zeroSet.indicator (fun point => values point))
  have restrictedAE : (fun point => restricted point) =ᵐ[law] zeroSet.indicator (fun point => values point) :=
    MemLp.coeFn_toLp restrictedMem
  have restrictedNonnegative : ∀ᵐ point ∂law, 0 ≤ restricted point := by
    filter_upwards [restrictedAE, valuesNonnegative] with point identity bound
    rw [identity]
    by_cases member : point ∈ zeroSet
    · simpa only [Set.indicator_of_mem member] using bound
    · simp only [Set.indicator_of_notMem member, le_refl]
  have restrictedLe : restricted ≤ values := by
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [restrictedAE, valuesNonnegative] with point identity bound
    rw [identity]
    by_cases member : point ∈ zeroSet
    · simp only [Set.indicator_of_mem member, le_refl]
    · simpa only [Set.indicator_of_notMem member] using bound
  have operatorMonotone : Monotone operator := by
    intro first second ordered
    have differenceNonnegative := positive (second - first)
      ((Lp.coeFn_nonneg _).mpr (sub_nonneg.mpr ordered))
    have differenceOrdered := (Lp.coeFn_nonneg _).mp differenceNonnegative
    rw [map_sub] at differenceOrdered
    exact sub_nonneg.mp differenceOrdered
  have pairZero : inner ℝ restricted (operator values) = 0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [restrictedAE] with point identity
    rw [identity]
    by_cases member : point ∈ zeroSet
    · have imageZero : operator values point = 0 := member
      simp only [Set.indicator_of_mem member, imageZero, inner_zero_right]
    · simp only [Set.indicator_of_notMem member, inner_zero_left]
  have pairingNonnegative := L2_inner_nonnegative_of_ae_nonnegative law restricted
    (operator values - operator restricted) restrictedNonnegative
    ((Lp.coeFn_nonneg _).mpr (sub_nonneg.mpr (operatorMonotone restrictedLe)))
  rw [inner_sub_right, pairZero] at pairingNonnegative
  have restrictedZero : restricted = 0 := by
    by_contra nonzero
    have strictlyPositive := strictPairing restricted nonzero
    linarith
  have restrictedZeroAE : ∀ᵐ point ∂law, restricted point = 0 := by
    rw [restrictedZero]
    exact Lp.coeFn_zero ℝ 2 law
  filter_upwards [restrictedAE, restrictedZeroAE] with point identity zero imageZero
  have member : point ∈ zeroSet := imageZero
  rw [Set.indicator_of_mem member] at identity
  exact identity.symm.trans zero

end IGS.Sec31

#print axioms IGS.Sec31.L2_inner_nonnegative_of_ae_nonnegative
#print axioms IGS.Sec31.L2_inner_eq_zero_iff_product_ae_zero
#print axioms IGS.Sec31.positive_L2_operator_zero_set_inclusion
