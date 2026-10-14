import RequestProject.Section31.EIGSTwoColourMatrixSpectra

/-! Exact actual edge-colour counts, derived by induction from the actual
substitution recursion. These are counting identities, not assumptions of
degree-distribution growth. Candidate source. -/

namespace EIGS
open scoped BigOperators
noncomputable section

theorem twoColourSystem_red_edge_recursion (level : ℕ) :
    (chiCount twoColourSystem.toRuleData (level + 1) 0 : ℝ) =
      3 * chiCount twoColourSystem.toRuleData level 0 +
        2 * chiCount twoColourSystem.toRuleData level 1 := by
  have equality := congrArg (fun vector => vector 0)
    (chiVec_succ twoColourSystem.toRuleData level)
  rw [twoColourSystem_massMatrixR] at equality
  simpa [chiVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val, mul_comm] using equality

theorem twoColourSystem_blue_edge_recursion (level : ℕ) :
    (chiCount twoColourSystem.toRuleData (level + 1) 1 : ℝ) =
      3 * chiCount twoColourSystem.toRuleData level 0 +
        3 * chiCount twoColourSystem.toRuleData level 1 := by
  have equality := congrArg (fun vector => vector 1)
    (chiVec_succ twoColourSystem.toRuleData level)
  rw [twoColourSystem_massMatrixR] at equality
  simpa [chiVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val, mul_comm] using equality

theorem twoColourSystem_edge_count_formulas (level : ℕ) :
    (chiCount twoColourSystem.toRuleData level 0 : ℝ) =
      ((3 + Real.sqrt 6) ^ level + (3 - Real.sqrt 6) ^ level) / 2 ∧
    (chiCount twoColourSystem.toRuleData level 1 : ℝ) =
      Real.sqrt 6 * ((3 + Real.sqrt 6) ^ level - (3 - Real.sqrt 6) ^ level) / 4 := by
  have square : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  induction level with
  | zero => norm_num [chiCount_zero, twoColourSystem, EIGSData.toRuleData]
  | succ level induction =>
      constructor
      · rw [twoColourSystem_red_edge_recursion, induction.1, induction.2, pow_succ, pow_succ]
        ring_nf <;> norm_num [square]
      · rw [twoColourSystem_blue_edge_recursion, induction.1, induction.2, pow_succ, pow_succ]
        ring_nf <;> norm_num [square]

theorem twoColourSystem_red_edge_growth_bounds (level : ℕ) :
    (3 + Real.sqrt 6) ^ level / 2 ≤ (chiCount twoColourSystem.toRuleData level 0 : ℝ) ∧
    (chiCount twoColourSystem.toRuleData level 0 : ℝ) ≤ (3 + Real.sqrt 6) ^ level := by
  have square : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have rootNonnegative := Real.sqrt_nonneg (6 : ℝ)
  have smallNonnegative : 0 ≤ 3 - Real.sqrt 6 := by nlinarith
  have smallPowerNonnegative := pow_nonneg smallNonnegative level
  have powerComparison : (3 - Real.sqrt 6) ^ level ≤ (3 + Real.sqrt 6) ^ level :=
    pow_le_pow_left₀ smallNonnegative (by linarith) level
  rw [(twoColourSystem_edge_count_formulas level).1]
  constructor <;> linarith

theorem twoColourSystem_blue_edge_upper (level : ℕ) :
    (chiCount twoColourSystem.toRuleData level 1 : ℝ) ≤ (3 + Real.sqrt 6) ^ level := by
  have square : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have rootNonnegative := Real.sqrt_nonneg (6 : ℝ)
  have rootUpper : Real.sqrt 6 ≤ 4 := by nlinarith
  have smallNonnegative : 0 ≤ 3 - Real.sqrt 6 := by nlinarith
  have smallPowerNonnegative := pow_nonneg smallNonnegative level
  have largePowerNonnegative := pow_nonneg (by linarith : 0 ≤ 3 + Real.sqrt 6) level
  have rootTimesSmallNonnegative := mul_nonneg rootNonnegative smallPowerNonnegative
  have rootTimesLargeUpper := mul_le_mul_of_nonneg_right rootUpper largePowerNonnegative
  rw [(twoColourSystem_edge_count_formulas level).2]
  nlinarith

end
end EIGS

#print axioms EIGS.twoColourSystem_edge_count_formulas
#print axioms EIGS.twoColourSystem_red_edge_growth_bounds
#print axioms EIGS.twoColourSystem_blue_edge_upper
