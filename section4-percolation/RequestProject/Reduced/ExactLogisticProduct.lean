import RequestProject.Reduced.Cases23
import Mathlib.Tactic

/-! The displayed rational logistic inequality for the actual reduced
resistance moments. A zero denominator is handled explicitly using total
real division; positivity of the ordinary denominator is a separate claim. -/

namespace Reduced
noncomputable section
set_option maxHeartbeats 4000000

theorem rational_logistic_of_cleared (relativeSecondMoment product nextProduct coefficient : ℝ)
    (relativeBound : 1 ≤ relativeSecondMoment) (productBound : 1 ≤ product)
    (cleared : ∀ larger, relativeSecondMoment ≤ larger →
      nextProduct * (larger * product - 1) ≤
        coefficient * ((larger - 1) * product ^ 2 + product - 1)) :
    nextProduct ≤ coefficient * product -
      coefficient * (product - 1) ^ 2 / (relativeSecondMoment * product - 1) := by
  have denominatorNonnegative : 0 ≤ relativeSecondMoment * product - 1 := by
    nlinarith
  by_cases zero : relativeSecondMoment * product - 1 = 0
  · have productOne : product = 1 := by nlinarith
    have relativeOne : relativeSecondMoment = 1 := by nlinarith [zero]
    have bound := cleared 2 (by linarith)
    simpa [productOne, relativeOne] using bound
  · have positive : 0 < relativeSecondMoment * product - 1 :=
      lt_of_le_of_ne denominatorNonnegative (Ne.symm zero)
    apply (le_sub_iff_add_le).mpr
    have bound := cleared relativeSecondMoment le_rfl
    have multiplied : nextProduct * (relativeSecondMoment * product - 1) +
        coefficient * (product - 1) ^ 2 ≤
          coefficient * product * (relativeSecondMoment * product - 1) := by nlinarith [bound]
    have divided := (div_le_iff₀ positive).mpr multiplied
    calc
      nextProduct + coefficient * (product - 1) ^ 2 / (relativeSecondMoment * product - 1) =
          (nextProduct * (relativeSecondMoment * product - 1) + coefficient * (product - 1) ^ 2) /
            (relativeSecondMoment * product - 1) := by
        rw [add_div, mul_div_cancel_right₀ _ zero]
      _ ≤ coefficient * product := divided

theorem logistic_product_exact_rational {pd ps : ℝ}
    (diamondNonnegative : 0 ≤ pd) (seriesNonnegative : 0 ≤ ps) (sumOne : ps + pd = 1)
    (generation : ℕ) :
    E1 pd ps (generation + 1) * Einv pd ps (generation + 1) ≤
      ((2 - pd) * (1 + pd) / 2) * (E1 pd ps generation * Einv pd ps generation) -
        ((2 - pd) * (1 + pd) / 2) * (E1 pd ps generation * Einv pd ps generation - 1) ^ 2 /
          (E2 pd ps generation * Einv pd ps generation / E1 pd ps generation - 1) := by
  have firstPositive : 0 < E1 pd ps generation :=
    zero_lt_one.trans_le (E1_ge_one diamondNonnegative seriesNonnegative sumOne generation)
  have squarePositive : 0 < (E1 pd ps generation) ^ 2 := sq_pos_of_pos firstPositive
  have relativeBound : 1 ≤ E2 pd ps generation / (E1 pd ps generation) ^ 2 :=
    (le_div_iff₀ squarePositive).mpr (by
      simpa only [one_mul] using E2_ge_E1sq diamondNonnegative seriesNonnegative sumOne generation)
  have bound := rational_logistic_of_cleared
    (E2 pd ps generation / (E1 pd ps generation) ^ 2)
    (E1 pd ps generation * Einv pd ps generation)
    (E1 pd ps (generation + 1) * Einv pd ps (generation + 1))
    ((2 - pd) * (1 + pd) / 2) relativeBound
    (E1Einv_ge_one diamondNonnegative seriesNonnegative sumOne generation) (by
      intro larger largerBound
      apply logistic_step diamondNonnegative seriesNonnegative sumOne larger generation
      exact (div_le_iff₀ squarePositive).mp largerBound)
  have denominatorEquality :
      E2 pd ps generation / (E1 pd ps generation) ^ 2 *
        (E1 pd ps generation * Einv pd ps generation) - 1 =
          E2 pd ps generation * Einv pd ps generation / E1 pd ps generation - 1 := by
    field_simp [firstPositive.ne']
    <;> ring
  rw [denominatorEquality] at bound
  exact bound

end
end Reduced

#print axioms Reduced.rational_logistic_of_cleared
#print axioms Reduced.logistic_product_exact_rational
