import RequestProject.Section31.SkorokhodJ1RightContinuousSeparation
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Hom.Set
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGS.Sec31.DiscreteMarkov

abbrev UnitJ1Time := Set.Icc (0 : ℝ) 1
noncomputable section
open Set
open scoped _root_.Topology

def intervalSingleKnotMove (pivot first second point : ℝ) : ℝ :=
  if point ≤ pivot then point else if point ≤ first then
    pivot + (point - pivot) * ((second - pivot) / (first - pivot))
  else second + (point - first) * ((1 - second) / (1 - first))

theorem intervalSingleKnotMove_strictMono
    (pivot first second : ℝ) (pivotBeforeFirst : pivot < first) (pivotBeforeSecond : pivot < second)
    (firstInterior : first < 1) (secondInterior : second < 1) :
    StrictMono (intervalSingleKnotMove pivot first second) := by
  have leftPositive : 0 < (second - pivot) / (first - pivot) := div_pos (sub_pos.mpr pivotBeforeSecond) (sub_pos.mpr pivotBeforeFirst)
  have rightPositive : 0 < (1 - second) / (1 - first) := div_pos (sub_pos.mpr secondInterior) (sub_pos.mpr firstInterior)
  have leftNonzero : first - pivot ≠ 0 := (sub_pos.mpr pivotBeforeFirst).ne'
  have leftEndpoint : (first - pivot) * ((second - pivot) / (first - pivot)) = second - pivot := by
    field_simp [leftNonzero]
  intro lower upper increasing
  unfold intervalSingleKnotMove
  by_cases lowerBefore : lower ≤ pivot
  · rw [if_pos lowerBefore]
    by_cases upperBefore : upper ≤ pivot
    · rw [if_pos upperBefore]
      exact increasing
    · rw [if_neg upperBefore]
      by_cases upperMiddle : upper ≤ first
      · rw [if_pos upperMiddle]
        have positivePart := mul_pos (sub_pos.mpr (lt_of_not_ge upperBefore)) leftPositive
        nlinarith
      · rw [if_neg upperMiddle]
        have positivePart := mul_pos (sub_pos.mpr (lt_of_not_ge upperMiddle)) rightPositive
        nlinarith
  · rw [if_neg lowerBefore]
    have upperBefore : ¬ upper ≤ pivot := by linarith
    rw [if_neg upperBefore]
    by_cases lowerMiddle : lower ≤ first
    · rw [if_pos lowerMiddle]
      by_cases upperMiddle : upper ≤ first
      · rw [if_pos upperMiddle]
        have increasingPart := mul_pos (sub_pos.mpr increasing) leftPositive
        nlinarith
      · rw [if_neg upperMiddle]
        have lowerGap := mul_nonneg (sub_nonneg.mpr lowerMiddle) leftPositive.le
        have upperGap := mul_pos (sub_pos.mpr (lt_of_not_ge upperMiddle)) rightPositive
        nlinarith
    · rw [if_neg lowerMiddle, if_neg (by linarith : ¬ upper ≤ first)]
      have increasingPart := mul_pos (sub_pos.mpr increasing) rightPositive
      nlinarith

theorem intervalSingleKnotMove_at_first
    (pivot first second : ℝ) (before : pivot < first) :
    intervalSingleKnotMove pivot first second first = second := by
  simp only [intervalSingleKnotMove, if_neg (not_le.mpr before), if_pos le_rfl]
  have nonzero : first - pivot ≠ 0 := (sub_pos.mpr before).ne'
  field_simp
  <;> ring

theorem intervalSingleKnotMove_at_one
    (pivot first second : ℝ) (pivotBefore : pivot < first) (firstInterior : first < 1) :
    intervalSingleKnotMove pivot first second 1 = 1 := by
  simp only [intervalSingleKnotMove, if_neg (by linarith : ¬ (1 : ℝ) ≤ pivot),
    if_neg (not_le.mpr firstInterior)]
  have nonzero : 1 - first ≠ 0 := (sub_pos.mpr firstInterior).ne'
  field_simp
  <;> ring

theorem intervalSingleKnotMove_continuous
    (pivot first second : ℝ) (before : pivot < first) :
    Continuous (intervalSingleKnotMove pivot first second) := by
  have middleContinuous : Continuous (fun point : ℝ => pivot + (point - pivot) * ((second - pivot) / (first - pivot))) := by fun_prop
  have rightContinuous : Continuous (fun point : ℝ => second + (point - first) * ((1 - second) / (1 - first))) := by fun_prop
  have atFirst : pivot + (first - pivot) * ((second - pivot) / (first - pivot)) =
      second + (first - first) * ((1 - second) / (1 - first)) := by
    have nonzero : first - pivot ≠ 0 := (sub_pos.mpr before).ne'
    field_simp
    <;> ring
  have innerContinuous : Continuous (fun point : ℝ => if point ≤ first then
      pivot + (point - pivot) * ((second - pivot) / (first - pivot)) else
      second + (point - first) * ((1 - second) / (1 - first))) := by
    exact middleContinuous.if (by intro point member; change point ∈ frontier (Iic first) at member; rw [frontier_Iic] at member; rcases mem_singleton_iff.mp member with rfl; exact atFirst) rightContinuous
  exact continuous_id.if (by
    intro point member
    change point ∈ frontier (Iic pivot) at member
    rw [frontier_Iic] at member
    rcases mem_singleton_iff.mp member with rfl
    simp only [if_pos before.le, sub_self, zero_mul, add_zero]) innerContinuous

theorem intervalSingleKnotMove_displacement
    (pivot first second point : ℝ) (pivotBeforeFirst : pivot < first) (firstInterior : first < 1)
    (pointNonnegative : 0 ≤ point) (pointAtMostOne : point ≤ 1) :
    |intervalSingleKnotMove pivot first second point - point| ≤ |second - first| := by
  unfold intervalSingleKnotMove
  by_cases before : point ≤ pivot
  · simp [before]
  · rw [if_neg before]
    by_cases middle : point ≤ first
    · rw [if_pos middle]
      have factorNonnegative : 0 ≤ (point - pivot) / (first - pivot) := div_nonneg (by linarith) (sub_pos.mpr pivotBeforeFirst).le
      have factorAtMostOne : (point - pivot) / (first - pivot) ≤ 1 := by
        rw [div_le_one₀ (sub_pos.mpr pivotBeforeFirst)]
        linarith
      have identity : pivot + (point - pivot) * ((second - pivot) / (first - pivot)) - point =
          ((point - pivot) / (first - pivot)) * (second - first) := by
        field_simp [(sub_pos.mpr pivotBeforeFirst).ne']
        <;> ring
      rw [identity, abs_mul, abs_of_nonneg factorNonnegative]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right factorAtMostOne (abs_nonneg (second - first))
    · rw [if_neg middle]
      have factorNonnegative : 0 ≤ (1 - point) / (1 - first) := div_nonneg (sub_nonneg.mpr pointAtMostOne) (sub_pos.mpr firstInterior).le
      have factorAtMostOne : (1 - point) / (1 - first) ≤ 1 := by
        rw [div_le_one₀ (sub_pos.mpr firstInterior)]
        linarith
      have identity : second + (point - first) * ((1 - second) / (1 - first)) - point =
          ((1 - point) / (1 - first)) * (second - first) := by
        field_simp [(sub_pos.mpr firstInterior).ne']
        <;> ring
      rw [identity, abs_mul, abs_of_nonneg factorNonnegative]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right factorAtMostOne (abs_nonneg (second - first))

theorem interval_single_knot_orderIso
    (pivot first second : UnitJ1Time)
    (pivotBeforeFirst : pivot < first) (pivotBeforeSecond : pivot < second)
    (firstInterior : first.val < 1) (secondInterior : second.val < 1) :
    ∃ change : UnitJ1Time ≃o UnitJ1Time,
      change first = second ∧
      (∀ point, point ≤ pivot → change point = point) ∧
      ∀ point, dist (change point) point ≤ dist first second := by
  have increasing := intervalSingleKnotMove_strictMono pivot.val first.val second.val
    pivotBeforeFirst pivotBeforeSecond firstInterior secondInterior
  have zeroValue : intervalSingleKnotMove pivot.val first.val second.val 0 = 0 := by
    simp [intervalSingleKnotMove, pivot.property.1]
  have oneValue := intervalSingleKnotMove_at_one pivot.val first.val second.val pivotBeforeFirst firstInterior
  have rangeValue : ∀ point : UnitJ1Time,
      intervalSingleKnotMove pivot.val first.val second.val point.val ∈ Icc (0 : ℝ) 1 := by
    intro point
    constructor
    · rw [← zeroValue]
      exact increasing.monotone point.property.1
    · rw [← oneValue]
      exact increasing.monotone point.property.2
  let function : UnitJ1Time → UnitJ1Time :=
    fun point => ⟨intervalSingleKnotMove pivot.val first.val second.val point.val, rangeValue point⟩
  have functionIncreasing : StrictMono function := fun _ _ below => increasing below
  have functionSurjective : Function.Surjective function := by
    intro target
    have intermediate := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
      (intervalSingleKnotMove_continuous pivot.val first.val second.val pivotBeforeFirst).continuousOn
    rw [zeroValue, oneValue] at intermediate
    obtain ⟨point, member, equality⟩ := intermediate target.property
    exact ⟨⟨point, member⟩, Subtype.ext equality⟩
  let change := functionIncreasing.orderIsoOfSurjective function functionSurjective
  refine ⟨change, ?_, ?_, ?_⟩
  · apply Subtype.ext
    exact intervalSingleKnotMove_at_first pivot.val first.val second.val pivotBeforeFirst
  · intro point below
    apply Subtype.ext
    exact if_pos below
  · intro point
    change |intervalSingleKnotMove pivot.val first.val second.val point.val - point.val| ≤ |first.val - second.val|
    rw [abs_sub_comm first.val second.val]
    exact intervalSingleKnotMove_displacement pivot.val first.val second.val point.val
      pivotBeforeFirst firstInterior point.property.1 point.property.2

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.intervalSingleKnotMove_strictMono
#print axioms IGS.Sec31.DiscreteMarkov.interval_single_knot_orderIso

