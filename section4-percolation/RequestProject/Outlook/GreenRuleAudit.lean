import RequestProject.Outlook.RuleCompatibility

/-! Exact enumeration of the four green-rule outcomes in figure/random_DHL.png.

Outcome order is the two top-row alternatives, the middle alternative and the
bottom alternative. Vertices are source=0, upper=1, sink=2, lower=3; edges run
source→upper→sink and source→lower→sink. Colours are red=0, blue=1, green=2,
black=3. This is an independently reviewable figure-derived correction
candidate. It does not modify the original displayed matrices.
-/

namespace Outlook.GreenRuleAudit

open scoped BigOperators

def source : Fin 4 → Fin 4 := ![0, 1, 0, 3]
def target : Fin 4 → Fin 4 := ![1, 2, 3, 2]
def colour : Fin 4 → Fin 4 → Fin 4 :=
  ![![0, 2, 2, 3], ![2, 3, 0, 2], ![0, 2, 0, 2], ![2, 3, 2, 3]]

def totalCount (outcome selected : Fin 4) : ℕ :=
  (Outlook.colourEdges Finset.univ (colour outcome) selected).card

def boundaryCount (outcome boundary selected : Fin 4) : ℕ :=
  (Outlook.boundaryColourEdges Finset.univ source (colour outcome) boundary selected).card

def incomingCount (outcome boundary selected : Fin 4) : ℕ :=
  (Outlook.boundaryColourEdges Finset.univ target (colour outcome) boundary selected).card

theorem red_total_counts : (fun outcome => totalCount outcome 0) = ![1, 1, 2, 0] := by
  decide
theorem red_positive_counts : (fun outcome => boundaryCount outcome 0 0) = ![1, 1, 2, 0] := by
  decide
theorem green_positive_counts : (fun outcome => boundaryCount outcome 0 2) = ![1, 1, 0, 2] := by
  decide
theorem green_negative_counts : (fun outcome => incomingCount outcome 2 2) = ![1, 1, 2, 0] := by
  decide

noncomputable def weights (p : ℝ) : Fin 4 → ℝ :=
  ![p / (1 + p) ^ 2, p / (1 + p) ^ 2, p ^ 2 / (1 + p) ^ 2, 1 / (1 + p) ^ 2]

noncomputable def figureWeights (p : ℝ) : Fin 4 → ℝ :=
  ![p * (1 - p) ^ 2 / ((1 - p) ^ 2 * (1 + p) ^ 2),
    p * (1 - p) ^ 2 / ((1 - p) ^ 2 * (1 + p) ^ 2),
    p ^ 2 * (1 - p) ^ 2 / ((1 - p) ^ 2 * (1 + p) ^ 2),
    (1 - p) ^ 2 / ((1 - p) ^ 2 * (1 + p) ^ 2)]

theorem figureWeights_eq_weights {p : ℝ} (positive : 0 < p) (below_one : p < 1) :
    figureWeights p = weights p := by
  have minus_ne : 1 - p ≠ 0 := (sub_pos.mpr below_one).ne'
  have plus_ne : 1 + p ≠ 0 := (by linarith : 0 < 1 + p).ne'
  ext outcome
  fin_cases outcome <;> dsimp [figureWeights, weights] <;> field_simp <;> ring

theorem weights_nonnegative {p : ℝ} (nonnegative : 0 ≤ p) :
    ∀ outcome, 0 ≤ weights p outcome := by
  intro outcome
  fin_cases outcome <;> dsimp [weights] <;> positivity

theorem weights_sum_one {p : ℝ} (nonnegative : 0 ≤ p) : ∑ outcome, weights p outcome = 1 := by
  have plus_ne : 1 + p ≠ 0 := (by linarith : 0 < 1 + p).ne'
  norm_num [weights, Fin.sum_univ_succ]
  field_simp
  ring

noncomputable def expected (p : ℝ) (counts : Fin 4 → ℕ) : ℝ :=
  ∑ outcome, weights p outcome * (counts outcome : ℝ)

theorem expected_red_total {p : ℝ} (nonnegative : 0 ≤ p) :
    expected p (fun outcome => totalCount outcome 0) = 2 * p / (1 + p) := by
  have plus_ne : 1 + p ≠ 0 := (by linarith : 0 < 1 + p).ne'
  rw [red_total_counts]
  norm_num [expected, weights, Fin.sum_univ_succ]
  field_simp
  ring

theorem expected_red_positive {p : ℝ} (nonnegative : 0 ≤ p) :
    expected p (fun outcome => boundaryCount outcome 0 0) = 2 * p / (1 + p) := by
  rw [red_positive_counts, ← red_total_counts]
  exact expected_red_total nonnegative

theorem expected_green_positive {p : ℝ} (nonnegative : 0 ≤ p) :
    expected p (fun outcome => boundaryCount outcome 0 2) = 2 / (1 + p) := by
  have plus_ne : 1 + p ≠ 0 := (by linarith : 0 < 1 + p).ne'
  rw [green_positive_counts]
  norm_num [expected, weights, Fin.sum_univ_succ]
  field_simp
  ring

theorem expected_green_negative {p : ℝ} (nonnegative : 0 ≤ p) :
    expected p (fun outcome => incomingCount outcome 2 2) = 2 * p / (1 + p) := by
  rw [green_negative_counts, ← red_total_counts]
  exact expected_red_total nonnegative

theorem critical_reciprocal : (1 + Reduced.pc)⁻¹ = Reduced.pc := by
  have plus_ne : 1 + Reduced.pc ≠ 0 := (by linarith [Reduced.pc_pos] : 0 < 1 + Reduced.pc).ne'
  have product_one : (1 + Reduced.pc) * Reduced.pc = 1 := by nlinarith [Reduced.pc_sq]
  calc
    (1 + Reduced.pc)⁻¹ = (1 + Reduced.pc)⁻¹ * 1 := by simp
    _ = (1 + Reduced.pc)⁻¹ * ((1 + Reduced.pc) * Reduced.pc) :=
      congrArg (fun value => (1 + Reduced.pc)⁻¹ * value) product_one.symm
    _ = Reduced.pc := by rw [← mul_assoc, inv_mul_cancel₀ plus_ne, one_mul]

theorem critical_figure_counts :
    expected Reduced.pc (fun outcome => totalCount outcome 0) = 2 * Reduced.pc ^ 2 ∧
    expected Reduced.pc (fun outcome => boundaryCount outcome 0 0) = 2 * Reduced.pc ^ 2 ∧
    expected Reduced.pc (fun outcome => boundaryCount outcome 0 2) = 2 * Reduced.pc ∧
    expected Reduced.pc (fun outcome => incomingCount outcome 2 2) = 2 * Reduced.pc ^ 2 := by
  rw [expected_red_total Reduced.pc_pos.le, expected_red_positive Reduced.pc_pos.le,
    expected_green_positive Reduced.pc_pos.le, expected_green_negative Reduced.pc_pos.le]
  simp only [div_eq_mul_inv, critical_reciprocal]
  constructor
  · ring
  constructor
  · ring
  constructor
  · trivial
  · ring

end Outlook.GreenRuleAudit
