import RequestProject.Section31.EIGSNativePoissonizedWalk

/-! Moments of the actual exponential-series weights used for the native
walk. These identities supply the fluctuation estimate needed to compare
the original discrete powers with their Poisson mixture. -/

namespace IGS.Sec31.PoissonizedWalk

open scoped BigOperators

theorem weight_succ_mul (parameter : ℝ) (jumps : ℕ) :
    weight parameter (jumps + 1) * (jumps + 1 : ℝ) =
      parameter * weight parameter jumps := by
  have factorialNonzero : (jumps.factorial : ℝ) ≠ 0 := by positivity
  have successorNonzero : (jumps + 1 : ℝ) ≠ 0 := by positivity
  simp only [weight, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp

theorem first_moment_hasSum (parameter : ℝ) :
    HasSum (fun jumps : ℕ => weight parameter jumps * jumps) parameter := by
  have shifted : HasSum (fun jumps : ℕ =>
      weight parameter (jumps + 1) * (jumps + 1 : ℝ)) parameter := by
    simpa only [weight_succ_mul, mul_one] using
      (weights_hasSum parameter).mul_left parameter
  simpa using (hasSum_nat_add_iff (f := fun jumps : ℕ =>
    weight parameter jumps * (jumps : ℝ)) 1).mp (by simpa using shifted)

theorem factorial_second_moment_hasSum (parameter : ℝ) :
    HasSum (fun jumps : ℕ => weight parameter jumps *
      (jumps : ℝ) * ((jumps : ℝ) - 1)) (parameter ^ 2) := by
  have shifted : HasSum (fun jumps : ℕ =>
      weight parameter (jumps + 1) * (jumps + 1 : ℝ) *
        ((jumps + 1 : ℝ) - 1)) (parameter ^ 2) := by
    convert (first_moment_hasSum parameter).mul_left parameter using 1
    · ext jumps
      rw [weight_succ_mul]
      ring
    · ring
  simpa using (hasSum_nat_add_iff (f := fun jumps : ℕ =>
    weight parameter jumps * (jumps : ℝ) * ((jumps : ℝ) - 1)) 1).mp
      (by simpa using shifted)

theorem second_moment_hasSum (parameter : ℝ) :
    HasSum (fun jumps : ℕ => weight parameter jumps * (jumps : ℝ) ^ 2)
      (parameter ^ 2 + parameter) := by
  convert (factorial_second_moment_hasSum parameter).add
    (first_moment_hasSum parameter) using 1
  ext jumps
  ring

theorem centered_second_moment_hasSum (parameter : ℝ) :
    HasSum (fun jumps : ℕ => weight parameter jumps * ((jumps : ℝ) - parameter) ^ 2)
      parameter := by
  convert ((second_moment_hasSum parameter).sub
    ((first_moment_hasSum parameter).mul_left (2 * parameter))).add
      ((weights_hasSum parameter).mul_left (parameter ^ 2)) using 1
  · ext jumps
    ring
  · ring

theorem absolute_deviation_partial_sum_le (parameter : ℝ)
    (parameterNonnegative : 0 ≤ parameter) (indices : Finset ℕ) :
    ∑ jumps ∈ indices, weight parameter jumps * |(jumps : ℝ) - parameter| ≤
      Real.sqrt parameter := by
  have weightSum : ∑ jumps ∈ indices, weight parameter jumps ≤ 1 := by
    calc
      _ ≤ ∑' jumps, weight parameter jumps :=
        (weights_hasSum parameter).summable.sum_le_tsum indices
          (fun jumps _ => weight_nonnegative parameter parameterNonnegative jumps)
      _ = 1 := (weights_hasSum parameter).tsum_eq
  have varianceSum : ∑ jumps ∈ indices,
      weight parameter jumps * ((jumps : ℝ) - parameter) ^ 2 ≤ parameter := by
    calc
      _ ≤ ∑' jumps, weight parameter jumps * ((jumps : ℝ) - parameter) ^ 2 :=
        (centered_second_moment_hasSum parameter).summable.sum_le_tsum indices
          (fun jumps _ => mul_nonneg (weight_nonnegative parameter parameterNonnegative jumps)
            (sq_nonneg _))
      _ = parameter := (centered_second_moment_hasSum parameter).tsum_eq
  have cauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul indices
    (r := fun jumps => weight parameter jumps * |(jumps : ℝ) - parameter|)
    (f := fun jumps => weight parameter jumps)
    (g := fun jumps => weight parameter jumps * ((jumps : ℝ) - parameter) ^ 2)
    (fun jumps _ => weight_nonnegative parameter parameterNonnegative jumps)
    (fun jumps _ => mul_nonneg (weight_nonnegative parameter parameterNonnegative jumps)
      (sq_nonneg _))
    (fun jumps _ => by rw [mul_pow, sq_abs]; ring)
  have varianceSumNonnegative : 0 ≤ ∑ jumps ∈ indices,
      weight parameter jumps * ((jumps : ℝ) - parameter) ^ 2 :=
    Finset.sum_nonneg fun jumps _ =>
      mul_nonneg (weight_nonnegative parameter parameterNonnegative jumps) (sq_nonneg _)
  have squaredBound := cauchy.trans ((mul_le_mul_of_nonneg_right weightSum
    varianceSumNonnegative).trans (by simpa using varianceSum))
  have := Real.sq_sqrt parameterNonnegative
  have := Real.sqrt_nonneg parameter
  nlinarith

theorem absolute_deviation_summable (parameter : ℝ)
    (parameterNonnegative : 0 ≤ parameter) :
    Summable (fun jumps : ℕ => weight parameter jumps * |(jumps : ℝ) - parameter|) :=
  summable_of_sum_le
    (fun jumps => mul_nonneg (weight_nonnegative parameter parameterNonnegative jumps) (abs_nonneg _))
    (absolute_deviation_partial_sum_le parameter parameterNonnegative)

theorem absolute_deviation_tsum_le (parameter : ℝ)
    (parameterNonnegative : 0 ≤ parameter) :
    ∑' jumps : ℕ, weight parameter jumps * |(jumps : ℝ) - parameter| ≤
      Real.sqrt parameter :=
  Real.tsum_le_of_sum_le
    (fun jumps => mul_nonneg (weight_nonnegative parameter parameterNonnegative jumps) (abs_nonneg _))
    (absolute_deviation_partial_sum_le parameter parameterNonnegative)

section Contraction

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [CompleteSpace Space]

noncomputable local instance : NormedAlgebra ℚ (Space →L[ℝ] Space) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

theorem contraction_power_apply_le (transition : Space →L[ℝ] Space)
    (contraction : ‖transition‖ ≤ 1) (jumps : ℕ) (values : Space) :
    ‖(transition ^ jumps) values‖ ≤ ‖values‖ := by
  induction jumps with
  | zero => simp
  | succ jumps induction =>
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      have bound : ‖transition ((transition ^ jumps) values)‖ ≤
          ‖(transition ^ jumps) values‖ := (transition.le_opNorm _).trans (by
        simpa using mul_le_mul_of_nonneg_right contraction
          (norm_nonneg ((transition ^ jumps) values)))
      exact bound.trans induction

theorem contraction_power_increment_le (transition : Space →L[ℝ] Space)
    (contraction : ‖transition‖ ≤ 1) (values : Space) (jumps extra : ℕ) :
    ‖(transition ^ (jumps + extra)) values - (transition ^ jumps) values‖ ≤
      (extra : ℝ) * ‖transition values - values‖ := by
  induction extra with
  | zero => simp
  | succ extra induction =>
      have step : (transition ^ (jumps + (extra + 1))) values -
          (transition ^ (jumps + extra)) values =
          (transition ^ (jumps + extra)) (transition values - values) := by
        rw [← Nat.add_assoc, pow_succ, ContinuousLinearMap.mul_apply, map_sub]
      have triangle := dist_triangle
        ((transition ^ (jumps + (extra + 1))) values)
        ((transition ^ (jumps + extra)) values) ((transition ^ jumps) values)
      simp only [dist_eq_norm] at triangle
      rw [step] at triangle
      have bound := contraction_power_apply_le transition contraction (jumps + extra)
        (transition values - values)
      push_cast
      nlinarith

theorem contraction_power_difference_le (transition : Space →L[ℝ] Space)
    (contraction : ‖transition‖ ≤ 1) (values : Space) (first second : ℕ) :
    ‖(transition ^ first) values - (transition ^ second) values‖ ≤
      |(first : ℝ) - second| * ‖transition values - values‖ := by
  rcases le_total second first with ordered | ordered
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le ordered
    simpa only [Nat.cast_add, add_sub_cancel_left,
      abs_of_nonneg (show (0 : ℝ) ≤ (extra : ℝ) from Nat.cast_nonneg extra)]
      using contraction_power_increment_le transition contraction values second extra
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le ordered
    rw [norm_sub_rev]
    simpa only [Nat.cast_add, sub_add_cancel_left, abs_neg,
      abs_of_nonneg (show (0 : ℝ) ≤ (extra : ℝ) from Nat.cast_nonneg extra)]
      using contraction_power_increment_le transition contraction values first extra

/-- The genuine discrete-power / Poisson-exponential comparison; no
semigroup convergence or de-Poissonization estimate is assumed. -/
theorem discrete_power_poisson_comparison (transition : Space →L[ℝ] Space)
    (contraction : ‖transition‖ ≤ 1) (values : Space) (jumps : ℕ) :
    ‖(NormedSpace.exp ((-(jumps : ℝ)) • (1 - transition))) values -
      (transition ^ jumps) values‖ ≤
        Real.sqrt jumps * ‖transition values - values‖ := by
  have differenceSum := (apply_hasSum transition 1 (jumps : ℝ) values).sub
    ((weights_hasSum (jumps : ℝ)).smul_const ((transition ^ jumps) values))
  simp only [mul_one, one_smul, ← smul_sub] at differenceSum
  have comparisonSum := (absolute_deviation_summable (jumps : ℝ)
    (Nat.cast_nonneg jumps)).hasSum.mul_right ‖transition values - values‖
  have bound := differenceSum.norm_le_of_bounded comparisonSum (fun other => by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (weight_nonnegative _ (Nat.cast_nonneg jumps) other)]
    exact (mul_le_mul_of_nonneg_left
      (contraction_power_difference_le transition contraction values other jumps)
      (weight_nonnegative _ (Nat.cast_nonneg jumps) other)).trans_eq (mul_assoc _ _ _).symm)
  exact bound.trans (mul_le_mul_of_nonneg_right
    (absolute_deviation_tsum_le (jumps : ℝ) (Nat.cast_nonneg jumps)) (norm_nonneg _))

end Contraction

end IGS.Sec31.PoissonizedWalk

#print axioms IGS.Sec31.PoissonizedWalk.weight_succ_mul
#print axioms IGS.Sec31.PoissonizedWalk.first_moment_hasSum
#print axioms IGS.Sec31.PoissonizedWalk.factorial_second_moment_hasSum
#print axioms IGS.Sec31.PoissonizedWalk.second_moment_hasSum
#print axioms IGS.Sec31.PoissonizedWalk.centered_second_moment_hasSum
#print axioms IGS.Sec31.PoissonizedWalk.absolute_deviation_partial_sum_le
#print axioms IGS.Sec31.PoissonizedWalk.absolute_deviation_summable
#print axioms IGS.Sec31.PoissonizedWalk.absolute_deviation_tsum_le
#print axioms IGS.Sec31.PoissonizedWalk.contraction_power_difference_le
#print axioms IGS.Sec31.PoissonizedWalk.discrete_power_poisson_comparison
