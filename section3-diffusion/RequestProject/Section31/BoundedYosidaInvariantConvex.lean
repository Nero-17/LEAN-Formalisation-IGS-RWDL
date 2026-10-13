import RequestProject.Section31.BoundedYosidaSemigroup
import Mathlib.Analysis.Convex.Combination

/-! The actual Yosida exponential preserves every closed convex set containing
zero that its resolvent preserves.  The proof uses its Poisson series. -/

namespace IGS.Sec31.BoundedYosida
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

theorem convex_sum_mem_of_sum_le_one (set : Set H) (convex : Convex ℝ set)
    (zero : (0 : H) ∈ set) (weights : ℕ → ℝ) (values : ℕ → H) (indices : Finset ℕ)
    (weightsNonnegative : ∀ index ∈ indices, 0 ≤ weights index)
    (weightsBound : ∑ index ∈ indices, weights index ≤ 1)
    (valuesMem : ∀ index ∈ indices, values index ∈ set) :
    ∑ index ∈ indices, weights index • values index ∈ set := by
  classical
  by_cases weightsZero : ∑ index ∈ indices, weights index = 0
  · have allZero := (Finset.sum_eq_zero_iff_of_nonneg weightsNonnegative).mp weightsZero
    have sumZero : ∑ index ∈ indices, weights index • values index = 0 := by
      apply Finset.sum_eq_zero
      intro index membership
      rw [allZero index membership, zero_smul]
    rw [sumZero]
    exact zero
  · have weightsPositive : 0 < ∑ index ∈ indices, weights index :=
      lt_of_le_of_ne (Finset.sum_nonneg weightsNonnegative) (Ne.symm weightsZero)
    have centreMem := convex.centerMass_mem weightsNonnegative weightsPositive valuesMem
    have scaled := convex.smul_mem_of_zero_mem zero centreMem
      ⟨weightsPositive.le, weightsBound⟩
    simpa only [Finset.centerMass, smul_smul, mul_inv_cancel₀ weightsZero, one_smul] using scaled

theorem poisson_weights_hasSum (parameter : ℝ) :
    HasSum (fun index : ℕ => Real.exp (-parameter) *
      ((index.factorial : ℝ)⁻¹ * parameter ^ index)) 1 := by
  have scalarSum : HasSum (fun index : ℕ =>
      ((index.factorial : ℝ)⁻¹) * parameter ^ index) (Real.exp parameter) := by
    simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) parameter)
  simpa only [smul_eq_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] using
    scalarSum.const_smul (Real.exp (-parameter))

theorem semigroup_hasSum_powers (resolvent : H →L[ℝ] H) (step time : ℝ) (values : H) :
    HasSum (fun index : ℕ =>
      (Real.exp (-(time / step)) * ((index.factorial : ℝ)⁻¹ * (time / step) ^ index)) •
        (resolvent ^ index) values) (semigroup resolvent step time values) := by
  have operatorSum := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
    ((time / step) • resolvent)).const_smul (Real.exp (-(time / step)))
  have valueSum := operatorSum.map (ContinuousLinearMap.apply ℝ H values)
    (ContinuousLinearMap.apply ℝ H values).continuous
  simpa only [semigroup_eq_scalar_mul_exp, map_smul, ContinuousLinearMap.apply_apply,
    smul_pow, ContinuousLinearMap.smul_apply, smul_smul, mul_assoc,
    Function.comp_apply] using valueSum

theorem semigroup_mem_of_closed_convex (resolvent : H →L[ℝ] H)
    (set : Set H) (closed : IsClosed set) (convex : Convex ℝ set) (zero : (0 : H) ∈ set)
    (resolventPreserves : Set.MapsTo resolvent set set)
    (step : ℝ) (stepPositive : 0 < step) (time : ℝ) (timeNonnegative : 0 ≤ time)
    (values : H) (valuesMem : values ∈ set) : semigroup resolvent step time values ∈ set := by
  have powersMem : ∀ index : ℕ, (resolvent ^ index) values ∈ set := by
    intro index
    induction index with
    | zero => simpa using valuesMem
    | succ index inductionMem =>
        simpa only [pow_succ', ContinuousLinearMap.mul_apply] using resolventPreserves inductionMem
  have weightsNonnegative : ∀ index : ℕ, 0 ≤
      Real.exp (-(time / step)) * ((index.factorial : ℝ)⁻¹ * (time / step) ^ index) := by
    intro index
    positivity
  have weightSum := poisson_weights_hasSum (time / step)
  apply closed.mem_of_tendsto (semigroup_hasSum_powers resolvent step time values)
  apply Filter.Eventually.of_forall
  intro indices
  apply convex_sum_mem_of_sum_le_one set convex zero _ _ indices
  · intro index _
    exact weightsNonnegative index
  · simpa only [weightSum.tsum_eq] using
      weightSum.summable.sum_le_tsum indices (fun index _ => weightsNonnegative index)
  · intro index _
    exact powersMem index

end IGS.Sec31.BoundedYosida

#print axioms IGS.Sec31.BoundedYosida.semigroup_hasSum_powers
#print axioms IGS.Sec31.BoundedYosida.semigroup_mem_of_closed_convex
