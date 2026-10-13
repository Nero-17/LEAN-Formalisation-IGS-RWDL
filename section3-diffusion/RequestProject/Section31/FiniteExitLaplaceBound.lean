import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace IGS.Sec31.DiscreteMarkov

open scoped BigOperators

/-- A substochastic collection of completed excursions. Missing mass may
represent an excursion that has not finished before the observation horizon. -/
theorem finite_subprobability_two_region_bound {Outcome : Type*} [Fintype Outcome]
    (weight payoff : Outcome → ℝ) (early : Outcome → Prop) [DecidablePred early]
    (probability decay : ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (totalBound : ∑ outcome, weight outcome ≤ 1)
    (earlyBound : (∑ outcome, if early outcome then weight outcome else 0) ≤ 1 - probability)
    (decayNonnegative : 0 ≤ decay) (decayBound : decay ≤ 1)
    (payoffBound : ∀ outcome, payoff outcome ≤ 1)
    (lateBound : ∀ outcome, ¬ early outcome → payoff outcome ≤ decay) :
    (∑ outcome, weight outcome * payoff outcome) ≤ 1 - probability * (1 - decay) := by
  calc
    _ ≤ ∑ outcome, (decay * weight outcome +
        (1 - decay) * (if early outcome then weight outcome else 0)) := by
      apply Finset.sum_le_sum
      intro outcome membership
      by_cases belongs : early outcome
      · rw [if_pos belongs]
        nlinarith [mul_le_mul_of_nonneg_left (payoffBound outcome) (weightNonnegative outcome)]
      · rw [if_neg belongs]
        nlinarith [mul_le_mul_of_nonneg_left (lateBound outcome belongs) (weightNonnegative outcome)]
    _ = decay * (∑ outcome, weight outcome) +
        (1 - decay) * (∑ outcome, if early outcome then weight outcome else 0) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ decay + (1 - decay) * (1 - probability) := by
      exact add_le_add (by simpa using mul_le_mul_of_nonneg_left totalBound decayNonnegative)
        (mul_le_mul_of_nonneg_left earlyBound (sub_nonneg.mpr decayBound))
    _ = 1 - probability * (1 - decay) := by ring

/-- A lower probability of waiting at least one time scale contracts the
Laplace transform of completed excursions, including finite-horizon truncation. -/
theorem finite_exit_laplace_bound {Outcome : Type*} [Fintype Outcome]
    (weight duration : Outcome → ℝ) (scale probability : ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (durationNonnegative : ∀ outcome, 0 ≤ duration outcome)
    (scalePositive : 0 < scale)
    (totalBound : ∑ outcome, weight outcome ≤ 1)
    (earlyBound : (∑ outcome, if duration outcome < scale then weight outcome else 0) ≤
      1 - probability) :
    (∑ outcome, weight outcome * Real.exp (-(duration outcome / scale))) ≤
      1 - probability * (1 - Real.exp (-1)) := by
  classical
  apply finite_subprobability_two_region_bound weight
    (fun outcome => Real.exp (-(duration outcome / scale)))
    (fun outcome => duration outcome < scale) probability (Real.exp (-1))
    weightNonnegative totalBound earlyBound (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by norm_num))
  · intro outcome
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
      (div_nonneg (durationNonnegative outcome) scalePositive.le))
  · intro outcome notEarly
    apply Real.exp_le_exp.mpr
    have ratio : 1 ≤ duration outcome / scale :=
      (le_div_iff₀ scalePositive).mpr (by simpa using le_of_not_gt notEarly)
    linarith

/-- The exponential Markov bound for the total duration of completed
excursions. A later stopping-time argument must supply its Laplace bound. -/
theorem finite_exit_probability_le_laplace {Outcome : Type*} [Fintype Outcome]
    (weight duration : Outcome → ℝ) (scale time : ℝ)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome) (scalePositive : 0 < scale) :
    (∑ outcome, if duration outcome ≤ time then weight outcome else 0) ≤
      Real.exp (time / scale) *
        (∑ outcome, weight outcome * Real.exp (-(duration outcome / scale))) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro outcome membership
  by_cases early : duration outcome ≤ time
  · rw [if_pos early]
    have exponential : 1 ≤ Real.exp (time / scale) * Real.exp (-(duration outcome / scale)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have division := div_le_div_of_nonneg_right early scalePositive.le
      linarith
    nlinarith [mul_le_mul_of_nonneg_left exponential (weightNonnegative outcome)]
  · rw [if_neg early]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (weightNonnegative outcome) (Real.exp_pos _).le)

theorem exit_laplace_contraction_lt_one (probability : ℝ) (positive : 0 < probability) :
    1 - probability * (1 - Real.exp (-1)) < 1 := by
  have exponential : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have product := mul_pos positive (sub_pos.mpr exponential)
  linarith

theorem exit_laplace_contraction_nonnegative (probability : ℝ)
    (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1) :
    0 ≤ 1 - probability * (1 - Real.exp (-1)) := by
  have exponential := (Real.exp_pos (-1)).le
  nlinarith [mul_nonneg nonnegative exponential]

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finite_subprobability_two_region_bound
#print axioms IGS.Sec31.DiscreteMarkov.finite_exit_laplace_bound
#print axioms IGS.Sec31.DiscreteMarkov.finite_exit_probability_le_laplace
#print axioms IGS.Sec31.DiscreteMarkov.exit_laplace_contraction_lt_one
#print axioms IGS.Sec31.DiscreteMarkov.exit_laplace_contraction_nonnegative
