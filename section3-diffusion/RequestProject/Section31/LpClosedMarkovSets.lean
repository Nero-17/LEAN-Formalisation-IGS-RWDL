import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Convex.Basic

/-! The almost-everywhere positive cone and unit interval are closed convex
subsets of real L2. Closedness follows from continuous Lipschitz truncations. -/
namespace IGS.Sec31.LpMarkov
open MeasureTheory
variable {X : Type*} [MeasurableSpace X] (measure : Measure X)

def nonnegativeSet : Set (Lp ℝ 2 measure) :=
  {values | ∀ᵐ point ∂measure, 0 ≤ values point}

def unitIntervalSet : Set (Lp ℝ 2 measure) :=
  {values | ∀ᵐ point ∂measure, 0 ≤ values point ∧ values point ≤ 1}

theorem nonnegativeSet_closed : IsClosed (nonnegativeSet measure) := by
  have lipschitz : LipschitzWith 1 (fun value : ℝ => max value 0) :=
    Lp.lipschitzWith_pos_part
  have zero : max (0 : ℝ) 0 = 0 := max_self _
  have fixedIff (values : Lp ℝ 2 measure) :
      lipschitz.compLp zero values = values ↔ values ∈ nonnegativeSet measure := by
    constructor
    · intro fixed
      have evaluation := lipschitz.coeFn_compLp zero values
      rw [fixed] at evaluation
      filter_upwards [evaluation] with point equality
      change values point = max (values point) 0 at equality
      rw [equality]
      exact le_max_right _ _
    · intro bounds
      apply Lp.ext
      filter_upwards [lipschitz.coeFn_compLp zero values, bounds] with point evaluation bound
      simpa only [Function.comp_apply, max_eq_left bound] using evaluation
  have equality : nonnegativeSet measure = {values | lipschitz.compLp zero values = values} := by
    ext values
    exact (fixedIff values).symm
  rw [equality]
  exact isClosed_eq (lipschitz.continuous_compLp zero) continuous_id

theorem unitIntervalSet_closed : IsClosed (unitIntervalSet measure) := by
  have lipschitz : LipschitzWith 1 (fun value : ℝ => min (max value 0) 1) :=
    Lp.lipschitzWith_pos_part.min_const 1
  have zero : min (max (0 : ℝ) 0) 1 = 0 := by norm_num
  have fixedIff (values : Lp ℝ 2 measure) :
      lipschitz.compLp zero values = values ↔ values ∈ unitIntervalSet measure := by
    constructor
    · intro fixed
      have evaluation := lipschitz.coeFn_compLp zero values
      rw [fixed] at evaluation
      filter_upwards [evaluation] with point equality
      change values point = min (max (values point) 0) 1 at equality
      rw [equality]
      exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
    · intro bounds
      apply Lp.ext
      filter_upwards [lipschitz.coeFn_compLp zero values, bounds] with point evaluation bound
      simpa only [Function.comp_apply, max_eq_left bound.1, min_eq_left bound.2] using evaluation
  have equality : unitIntervalSet measure = {values | lipschitz.compLp zero values = values} := by
    ext values
    exact (fixedIff values).symm
  rw [equality]
  exact isClosed_eq (lipschitz.continuous_compLp zero) continuous_id

theorem zero_mem_nonnegativeSet : (0 : Lp ℝ 2 measure) ∈ nonnegativeSet measure := by
  filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := measure)] with point equality
  simpa only [equality, Pi.zero_apply] using (le_refl (0 : ℝ))

theorem zero_mem_unitIntervalSet : (0 : Lp ℝ 2 measure) ∈ unitIntervalSet measure := by
  filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := measure)] with point equality
  simpa only [equality, Pi.zero_apply] using (show 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 by norm_num)

theorem nonnegativeSet_convex : Convex ℝ (nonnegativeSet measure) := by
  intro first firstMem second secondMem firstWeight secondWeight firstNonnegative secondNonnegative sumOne
  change ∀ᵐ point ∂measure, 0 ≤ (firstWeight • first + secondWeight • second) point
  change ∀ᵐ point ∂measure, 0 ≤ first point at firstMem
  change ∀ᵐ point ∂measure, 0 ≤ second point at secondMem
  filter_upwards [Lp.coeFn_add (firstWeight • first) (secondWeight • second),
    Lp.coeFn_smul firstWeight first, Lp.coeFn_smul secondWeight second,
    firstMem, secondMem] with point addition firstEvaluation secondEvaluation firstBound secondBound
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at addition firstEvaluation secondEvaluation
  rw [addition, firstEvaluation, secondEvaluation]
  exact add_nonneg (mul_nonneg firstNonnegative firstBound) (mul_nonneg secondNonnegative secondBound)

theorem unitIntervalSet_convex : Convex ℝ (unitIntervalSet measure) := by
  intro first firstMem second secondMem firstWeight secondWeight firstNonnegative secondNonnegative sumOne
  change ∀ᵐ point ∂measure,
    0 ≤ (firstWeight • first + secondWeight • second) point ∧
    (firstWeight • first + secondWeight • second) point ≤ 1
  change ∀ᵐ point ∂measure, 0 ≤ first point ∧ first point ≤ 1 at firstMem
  change ∀ᵐ point ∂measure, 0 ≤ second point ∧ second point ≤ 1 at secondMem
  filter_upwards [Lp.coeFn_add (firstWeight • first) (secondWeight • second),
    Lp.coeFn_smul firstWeight first, Lp.coeFn_smul secondWeight second,
    firstMem, secondMem] with point addition firstEvaluation secondEvaluation firstBound secondBound
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at addition firstEvaluation secondEvaluation
  rw [addition, firstEvaluation, secondEvaluation]
  constructor
  · exact add_nonneg (mul_nonneg firstNonnegative firstBound.1) (mul_nonneg secondNonnegative secondBound.1)
  · calc
      firstWeight * first point + secondWeight * second point ≤ firstWeight * 1 + secondWeight * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left firstBound.2 firstNonnegative)
          (mul_le_mul_of_nonneg_left secondBound.2 secondNonnegative)
      _ = 1 := by simpa only [mul_one] using sumOne

end IGS.Sec31.LpMarkov

#print axioms IGS.Sec31.LpMarkov.nonnegativeSet_closed
#print axioms IGS.Sec31.LpMarkov.unitIntervalSet_closed
#print axioms IGS.Sec31.LpMarkov.nonnegativeSet_convex
#print axioms IGS.Sec31.LpMarkov.unitIntervalSet_convex
