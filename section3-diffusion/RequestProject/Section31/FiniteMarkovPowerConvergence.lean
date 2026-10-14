import RequestProject.Section31.FiniteMarkovVectorRange

/-! Finite stochastic powers converge to a constant on each real column
vector when an actual power has a common positive column. The proof uses
monotone finite envelopes and the proved geometric width contraction.
Candidate source. -/

namespace EIGS
open Filter Topology
open scoped BigOperators
noncomputable section
variable {State : Type*} [Fintype State] [DecidableEq State] [Nonempty State]

theorem finiteMarkov_common_column_envelope_convergence (kernel : Matrix State State ℝ)
    (nonnegative : ∀ first second, 0 ≤ kernel first second)
    (rowSum : ∀ first, ∑ second, kernel first second = 1)
    (anchor : State) (commonMass : ℝ) (commonMassPositive : 0 < commonMass)
    (commonMassSmall : commonMass < 1)
    (commonColumn : ∀ first, commonMass ≤ kernel first anchor)
    (function : State → ℝ) :
    ∃ value : ℝ, finiteVectorMinimum function ≤ value ∧
      Tendsto (fun power : ℕ => finiteVectorMinimum ((kernel ^ power).mulVec function))
        atTop (𝓝 value) ∧
      Tendsto (fun power : ℕ => finiteVectorMaximum ((kernel ^ power).mulVec function))
        atTop (𝓝 value) := by
  have monotonicity := finiteMarkov_power_envelopes kernel nonnegative rowSum function
  have widthBound (power : ℕ) :
      finiteVectorWidth ((kernel ^ power).mulVec function) ≤
        (1 - commonMass) ^ power * finiteVectorWidth function := by
    induction power with
    | zero => simp
    | succ power induction =>
        have comparison := finiteMarkov_width_contraction kernel nonnegative rowSum
          anchor commonMass commonColumn ((kernel ^ power).mulVec function)
        calc
          finiteVectorWidth ((kernel ^ (power + 1)).mulVec function) ≤
              (1 - commonMass) * finiteVectorWidth ((kernel ^ power).mulVec function) := by
                simpa only [pow_succ', Matrix.mulVec_mulVec] using comparison
          _ ≤ (1 - commonMass) * ((1 - commonMass) ^ power * finiteVectorWidth function) :=
            mul_le_mul_of_nonneg_left induction (sub_nonneg.mpr commonMassSmall.le)
          _ = (1 - commonMass) ^ (power + 1) * finiteVectorWidth function := by
            rw [pow_succ]
            ring
  have powerDecay : Tendsto (fun power : ℕ => (1 - commonMass) ^ power) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by
      rw [abs_of_pos (sub_pos.mpr commonMassSmall)]
      linarith)
  have widthDecay : Tendsto
      (fun power : ℕ => finiteVectorWidth ((kernel ^ power).mulVec function)) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (by simpa using powerDecay.mul_const (finiteVectorWidth function))
    · intro power
      exact finiteVector_width_nonnegative _
    · exact widthBound
  have lowerBounded : BddAbove (Set.range
      (fun power : ℕ => finiteVectorMinimum ((kernel ^ power).mulVec function))) := by
    refine ⟨finiteVectorMaximum function, ?_⟩
    rintro value ⟨power, rfl⟩
    have range := finiteVector_range_bounds ((kernel ^ power).mulVec function)
      (Classical.arbitrary State)
    have upper := monotonicity.2 (Nat.zero_le power)
    simp only [pow_zero, Matrix.one_mulVec] at upper
    exact (range.1.trans range.2).trans upper
  have lowerConvergence := tendsto_atTop_ciSup monotonicity.1 lowerBounded
  refine ⟨⨆ power : ℕ, finiteVectorMinimum ((kernel ^ power).mulVec function), ?_,
    lowerConvergence, ?_⟩
  · have comparison := le_ciSup lowerBounded (0 : ℕ)
    simpa only [pow_zero, Matrix.one_mulVec] using comparison
  · have convergence := lowerConvergence.add widthDecay
    simpa only [finiteVectorWidth, ← add_sub_assoc, add_sub_cancel_left, add_zero] using convergence

theorem finiteMarkov_power_convergence_of_common_power (kernel : Matrix State State ℝ)
    (nonnegative : ∀ first second, 0 ≤ kernel first second)
    (rowSum : ∀ first, ∑ second, kernel first second = 1)
    (block : ℕ) (blockPositive : 0 < block)
    (anchor : State) (commonMass : ℝ) (commonMassPositive : 0 < commonMass)
    (commonMassSmall : commonMass < 1)
    (commonColumn : ∀ first, commonMass ≤ (kernel ^ block) first anchor)
    (function : State → ℝ) :
    ∃ value : ℝ, finiteVectorMinimum function ≤ value ∧
      ∀ state, Tendsto (fun power : ℕ => ((kernel ^ power).mulVec function) state)
        atTop (𝓝 value) := by
  have stochastic : kernel ∈ Matrix.rowStochastic ℝ State :=
    Matrix.mem_rowStochastic_iff_sum.2 ⟨nonnegative, rowSum⟩
  have powerStochastic := (Matrix.rowStochastic ℝ State).pow_mem stochastic block
  obtain ⟨value, lowerBound, lowerConvergence, upperConvergence⟩ :=
    finiteMarkov_common_column_envelope_convergence (kernel ^ block)
      (fun first second => Matrix.nonneg_of_mem_rowStochastic powerStochastic)
      (Matrix.sum_row_of_mem_rowStochastic powerStochastic)
      anchor commonMass commonMassPositive commonMassSmall commonColumn function
  have divisionTendsto : Tendsto (fun power : ℕ => power / block) atTop atTop := by
    apply tendsto_atTop.2
    intro threshold
    exact eventually_atTop.2 ⟨threshold * block, fun power bound =>
      (Nat.le_div_iff_mul_le blockPositive).2 bound⟩
  have monotonicity := finiteMarkov_power_envelopes kernel nonnegative rowSum function
  refine ⟨value, lowerBound, ?_⟩
  intro state
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (lowerConvergence.comp divisionTendsto) (upperConvergence.comp divisionTendsto)
  · intro power
    have depthBound : block * (power / block) ≤ power := by
      simpa only [Nat.mul_comm] using Nat.div_mul_le_self power block
    have lower := monotonicity.1 depthBound
    have range := (finiteVector_range_bounds ((kernel ^ power).mulVec function) state).1
    simpa only [← pow_mul] using lower.trans range
  · intro power
    have depthBound : block * (power / block) ≤ power := by
      simpa only [Nat.mul_comm] using Nat.div_mul_le_self power block
    have upper := monotonicity.2 depthBound
    have range := (finiteVector_range_bounds ((kernel ^ power).mulVec function) state).2
    simpa only [← pow_mul] using range.trans upper

end
end EIGS

#print axioms EIGS.finiteMarkov_common_column_envelope_convergence
#print axioms EIGS.finiteMarkov_power_convergence_of_common_power
