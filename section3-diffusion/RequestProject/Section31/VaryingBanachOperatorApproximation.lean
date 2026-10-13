import RequestProject.Section31.EIGSNativeYosidaConvergence

/-! Operator approximation through bounded restriction maps in varying
Banach spaces. Convergence is the norm of the actual restriction error,
not varying L² Strong convergence. -/

namespace IGS.Sec31.VaryingBanachOperatorApproximation

open Filter Topology
open scoped BigOperators

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  {LevelSpace : ℕ → Type*} [∀ level, NormedAddCommGroup (LevelSpace level)]
  [∀ level, NormedSpace ℝ (LevelSpace level)]

theorem varying_apply
    (restriction : ∀ level, Space →L[ℝ] LevelSpace level)
    (operators : ∀ level, LevelSpace level →L[ℝ] LevelSpace level)
    (operator : Space →L[ℝ] Space) (bound : ℝ)
    (operatorBound : ∀ level, ‖operators level‖ ≤ bound)
    (operatorConvergence : ∀ values : Space,
      Tendsto (fun level => ‖operators level (restriction level values) -
        restriction level (operator values)‖) atTop (nhds 0))
    (sequence : ∀ level, LevelSpace level) (values : Space)
    (convergence : Tendsto (fun level => ‖sequence level - restriction level values‖) atTop (nhds 0)) :
    Tendsto (fun level => ‖operators level (sequence level) - restriction level (operator values)‖)
      atTop (nhds 0) := by
  have comparison (level : ℕ) :
      ‖operators level (sequence level) - restriction level (operator values)‖ ≤
        bound * ‖sequence level - restriction level values‖ +
          ‖operators level (restriction level values) - restriction level (operator values)‖ := by
    calc
      _ ≤ ‖operators level (sequence level) - operators level (restriction level values)‖ +
          ‖operators level (restriction level values) - restriction level (operator values)‖ :=
        by simpa only [dist_eq_norm] using
          dist_triangle (operators level (sequence level))
            (operators level (restriction level values)) (restriction level (operator values))
      _ ≤ _ := by
        refine add_le_add ?_ le_rfl
        rw [← map_sub]
        exact (operators level).le_of_opNorm_le (operatorBound level) _
  have upperLimit := (convergence.const_mul bound).add (operatorConvergence values)
  apply squeeze_zero (fun _ => norm_nonneg _) comparison
  simpa only [mul_zero, zero_add] using upperLimit

theorem powers_apply
    (restriction : ∀ level, Space →L[ℝ] LevelSpace level)
    (operators : ∀ level, LevelSpace level →L[ℝ] LevelSpace level)
    (operator : Space →L[ℝ] Space) (bound : ℝ)
    (operatorBound : ∀ level, ‖operators level‖ ≤ bound)
    (operatorConvergence : ∀ values : Space,
      Tendsto (fun level => ‖operators level (restriction level values) -
        restriction level (operator values)‖) atTop (nhds 0))
    (values : Space) (power : ℕ) :
    Tendsto (fun level => ‖(operators level ^ power) (restriction level values) -
      restriction level ((operator ^ power) values)‖) atTop (nhds 0) := by
  induction power with
  | zero => simpa only [pow_zero, ContinuousLinearMap.one_apply, sub_self, norm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  | succ power induction =>
      simpa only [pow_succ', ContinuousLinearMap.mul_apply] using
        varying_apply restriction operators operator bound operatorBound operatorConvergence
          (fun level => (operators level ^ power) (restriction level values))
          ((operator ^ power) values) induction

theorem polynomial_apply
    (restriction : ∀ level, Space →L[ℝ] LevelSpace level)
    (operators : ∀ level, LevelSpace level →L[ℝ] LevelSpace level)
    (operator : Space →L[ℝ] Space) (bound : ℝ)
    (operatorBound : ∀ level, ‖operators level‖ ≤ bound)
    (operatorConvergence : ∀ values : Space,
      Tendsto (fun level => ‖operators level (restriction level values) -
        restriction level (operator values)‖) atTop (nhds 0))
    (values : Space) (depth : ℕ) :
    Tendsto (fun level => ‖VaryingBoundedExponential.polynomial (operators level) depth
      (restriction level values) - restriction level
        (VaryingBoundedExponential.polynomial operator depth values)‖) atTop (nhds 0) := by
  have expansion (level : ℕ) :
      VaryingBoundedExponential.polynomial (operators level) depth (restriction level values) -
        restriction level (VaryingBoundedExponential.polynomial operator depth values) =
      ∑ index ∈ Finset.range depth, (index.factorial : ℝ)⁻¹ •
        ((operators level ^ index) (restriction level values) - restriction level ((operator ^ index) values)) := by
    simp only [VaryingBoundedExponential.polynomial, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
  have comparison (level : ℕ) :
      ‖VaryingBoundedExponential.polynomial (operators level) depth (restriction level values) -
        restriction level (VaryingBoundedExponential.polynomial operator depth values)‖ ≤
      ∑ index ∈ Finset.range depth, (index.factorial : ℝ)⁻¹ *
        ‖(operators level ^ index) (restriction level values) - restriction level ((operator ^ index) values)‖ := by
    rw [expansion]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro index _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (index.factorial : ℝ)⁻¹)]
  have upperLimit := tendsto_finset_sum (Finset.range depth) (fun index _ =>
    (powers_apply restriction operators operator bound operatorBound operatorConvergence values index).const_mul
      (index.factorial : ℝ)⁻¹)
  apply squeeze_zero (fun _ => norm_nonneg _) comparison
  simpa only [mul_zero, Finset.sum_const_zero] using upperLimit

theorem exponential_apply [CompleteSpace Space] [∀ level, CompleteSpace (LevelSpace level)]
    (restriction : ∀ level, Space →L[ℝ] LevelSpace level)
    (restrictionBound : ∀ level, ‖restriction level‖ ≤ 1)
    (operators : ∀ level, LevelSpace level →L[ℝ] LevelSpace level)
    (operator : Space →L[ℝ] Space) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (operatorBound : ∀ level, ‖operators level‖ ≤ bound) (limitBound : ‖operator‖ ≤ bound)
    (operatorConvergence : ∀ values : Space,
      Tendsto (fun level => ‖operators level (restriction level values) -
        restriction level (operator values)‖) atTop (nhds 0))
    (values : Space) :
    Tendsto (fun level => ‖NormedSpace.exp (operators level) (restriction level values) -
      restriction level (NormedSpace.exp operator values)‖) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro tolerance tolerancePositive
  have tailLimit : Tendsto (fun depth => 2 * ‖values‖ * VaryingBoundedExponential.scalarTail bound depth)
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (VaryingBoundedExponential.scalarTail_tendsto bound).const_mul (2 * ‖values‖)
  obtain ⟨depth, tailSmall⟩ :=
    (tailLimit.eventually_lt_const (half_pos tolerancePositive)).exists
  have polynomialLimit := polynomial_apply restriction operators operator bound operatorBound
    operatorConvergence values depth
  obtain ⟨threshold, polynomialSmall⟩ := eventually_atTop.mp
    (polynomialLimit.eventually_lt_const (half_pos tolerancePositive))
  refine ⟨threshold, ?_⟩
  intro level afterThreshold
  have restrictionValues : ‖restriction level values‖ ≤ ‖values‖ := by
    simpa only [one_mul] using (restriction level).le_of_opNorm_le (restrictionBound level) values
  have tailNonnegative : 0 ≤ VaryingBoundedExponential.scalarTail bound depth :=
    (norm_nonneg _).trans (VaryingBoundedExponential.norm_exp_sub_polynomial_le
      operator bound boundNonnegative limitBound depth)
  have finiteTail :
      ‖NormedSpace.exp (operators level) (restriction level values) -
        VaryingBoundedExponential.polynomial (operators level) depth (restriction level values)‖ ≤
      VaryingBoundedExponential.scalarTail bound depth * ‖values‖ := by
    change ‖(NormedSpace.exp (operators level) -
      VaryingBoundedExponential.polynomial (operators level) depth) (restriction level values)‖ ≤ _
    exact ((NormedSpace.exp (operators level) - VaryingBoundedExponential.polynomial (operators level) depth).le_of_opNorm_le
      (VaryingBoundedExponential.norm_exp_sub_polynomial_le
        (operators level) bound boundNonnegative (operatorBound level) depth) _).trans
      (mul_le_mul_of_nonneg_left restrictionValues tailNonnegative)
  have limitTail :
      ‖VaryingBoundedExponential.polynomial operator depth values - NormedSpace.exp operator values‖ ≤
      VaryingBoundedExponential.scalarTail bound depth * ‖values‖ := by
    rw [norm_sub_rev]
    change ‖(NormedSpace.exp operator - VaryingBoundedExponential.polynomial operator depth) values‖ ≤ _
    exact (NormedSpace.exp operator - VaryingBoundedExponential.polynomial operator depth).le_of_opNorm_le
      (VaryingBoundedExponential.norm_exp_sub_polynomial_le
        operator bound boundNonnegative limitBound depth) values
  have restrictedTail :
      ‖restriction level (VaryingBoundedExponential.polynomial operator depth values) -
        restriction level (NormedSpace.exp operator values)‖ ≤
      VaryingBoundedExponential.scalarTail bound depth * ‖values‖ := by
    rw [← map_sub]
    exact ((restriction level).le_of_opNorm_le (restrictionBound level) _).trans
      (by simpa only [one_mul] using limitTail)
  have firstTriangle := dist_triangle
    (NormedSpace.exp (operators level) (restriction level values))
    (VaryingBoundedExponential.polynomial (operators level) depth (restriction level values))
    (restriction level (NormedSpace.exp operator values))
  have secondTriangle := dist_triangle
    (VaryingBoundedExponential.polynomial (operators level) depth (restriction level values))
    (restriction level (VaryingBoundedExponential.polynomial operator depth values))
    (restriction level (NormedSpace.exp operator values))
  simp only [dist_eq_norm] at firstTriangle secondTriangle
  have totalSmall : ‖NormedSpace.exp (operators level) (restriction level values) -
      restriction level (NormedSpace.exp operator values)‖ < tolerance := by
    have middleSmall := polynomialSmall level afterThreshold
    nlinarith
  simpa only [dist_zero_right, norm_norm] using totalSmall

theorem yosida_exponential_apply [CompleteSpace Space] [∀ level, CompleteSpace (LevelSpace level)]
    (restriction : ∀ level, Space →L[ℝ] LevelSpace level)
    (restrictionBound : ∀ level, ‖restriction level‖ ≤ 1)
    (resolvers : ∀ level, LevelSpace level →L[ℝ] LevelSpace level)
    (resolver : Space →L[ℝ] Space)
    (resolverBound : ∀ level, ‖resolvers level‖ ≤ 1) (limitBound : ‖resolver‖ ≤ 1)
    (resolverConvergence : ∀ values : Space,
      Tendsto (fun level => ‖resolvers level (restriction level values) -
        restriction level (resolver values)‖) atTop (nhds 0))
    (step : ℝ) (stepPositive : 0 < step) (time : ℝ) (values : Space) :
    Tendsto (fun level => ‖BoundedYosida.semigroup (resolvers level) step time
      (restriction level values) - restriction level (BoundedYosida.semigroup resolver step time values)‖)
      atTop (nhds 0) := by
  have finiteBound (level : ℕ) :
      ‖(-time) • BoundedYosida.generator (resolvers level) step‖ ≤ |time| * (2 / step) := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    exact mul_le_mul_of_nonneg_left
      (VaryingBoundedExponential.yosida_generator_norm_bound (resolvers level)
        (resolverBound level) step stepPositive) (abs_nonneg time)
  have targetBound : ‖(-time) • BoundedYosida.generator resolver step‖ ≤ |time| * (2 / step) := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    exact mul_le_mul_of_nonneg_left
      (VaryingBoundedExponential.yosida_generator_norm_bound resolver limitBound step stepPositive)
      (abs_nonneg time)
  have generatorsConverge (argument : Space) :
      Tendsto (fun level => ‖((-time) • BoundedYosida.generator (resolvers level) step)
        (restriction level argument) - restriction level
          (((-time) • BoundedYosida.generator resolver step) argument)‖) atTop (nhds 0) := by
    have identity (level : ℕ) :
        ((-time) • BoundedYosida.generator (resolvers level) step) (restriction level argument) -
          restriction level (((-time) • BoundedYosida.generator resolver step) argument) =
        (time / step) • (resolvers level (restriction level argument) - restriction level (resolver argument)) := by
      change (-time) • (step⁻¹ • (restriction level argument -
        resolvers level (restriction level argument))) -
        restriction level ((-time) • (step⁻¹ • (argument - resolver argument))) = _
      rw [map_smul, map_smul, map_sub]
      simp only [smul_smul, div_eq_mul_inv, neg_mul, neg_smul, smul_sub]
      module
    simp_rw [identity, norm_smul, Real.norm_eq_abs]
    simpa only [mul_zero] using (resolverConvergence argument).const_mul |time / step|
  exact exponential_apply restriction restrictionBound
    (fun level => (-time) • BoundedYosida.generator (resolvers level) step)
    ((-time) • BoundedYosida.generator resolver step) (|time| * (2 / step))
    (by positivity) finiteBound targetBound generatorsConverge values

end IGS.Sec31.VaryingBanachOperatorApproximation

#print axioms IGS.Sec31.VaryingBanachOperatorApproximation.varying_apply
#print axioms IGS.Sec31.VaryingBanachOperatorApproximation.powers_apply
#print axioms IGS.Sec31.VaryingBanachOperatorApproximation.polynomial_apply
#print axioms IGS.Sec31.VaryingBanachOperatorApproximation.exponential_apply
#print axioms IGS.Sec31.VaryingBanachOperatorApproximation.yosida_exponential_apply
