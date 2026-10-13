import RequestProject.Outlook.Matrices
import RequestProject.Reduced.Params

/-!
# A necessary compatibility condition for the two rule-count matrices

The original definitions count all colour-j edges in `M[i,j]`, and outgoing
colour-j edges at one boundary of the same rule in `N[2*i,2*j]` (zero-based).
The latter set is a subset of the former, for every rule realization.

The displayed green/red entries in Subsection 4.2 violate this necessary
condition for every parameter strictly between zero and one. The theorem
below diagnoses the incompatibility; it does not propose a corrected matrix.
-/

namespace Outlook

open MeasureTheory

variable {Edge Vertex : Type*}

/-- All edges of the selected colour in a finite rule. -/
def colourEdges (edges : Finset Edge) (colour : Edge → Fin 4) (selected : Fin 4) :
    Finset Edge := edges.filter (fun edge => colour edge = selected)

/-- Outgoing edges of the selected colour at a boundary of that same rule. -/
def boundaryColourEdges (edges : Finset Edge) (source : Edge → Vertex)
    (colour : Edge → Fin 4) (boundary : Vertex) (selected : Fin 4)
    [DecidableEq Vertex] : Finset Edge :=
  edges.filter (fun edge => colour edge = selected ∧ source edge = boundary)

theorem boundaryColourEdges_subset [DecidableEq Vertex]
    (edges : Finset Edge) (source : Edge → Vertex) (colour : Edge → Fin 4)
    (boundary : Vertex) (selected : Fin 4) :
    boundaryColourEdges edges source colour boundary selected ⊆
      colourEdges edges colour selected := by
  intro edge membership
  simp only [boundaryColourEdges, Finset.mem_filter] at membership
  exact Finset.mem_filter.mpr ⟨membership.1, membership.2.1⟩

theorem boundaryColourEdges_card_le [DecidableEq Vertex]
    (edges : Finset Edge) (source : Edge → Vertex) (colour : Edge → Fin 4)
    (boundary : Vertex) (selected : Fin 4) :
    (boundaryColourEdges edges source colour boundary selected).card ≤
      (colourEdges edges colour selected).card :=
  Finset.card_le_card (boundaryColourEdges_subset edges source colour boundary selected)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Counts in a fixed finite edge universe are integrable whenever measurable. -/
theorem integrable_card [Fintype Edge] (measure : Measure Ω) [IsFiniteMeasure measure]
    (edges : Ω → Finset Edge)
    (measurable_count : Measurable (fun outcome => ((edges outcome).card : ℝ))) :
    Integrable (fun outcome => ((edges outcome).card : ℝ)) measure := by
  apply (integrable_const (Fintype.card Edge : ℝ)).mono'
    measurable_count.aestronglyMeasurable
  filter_upwards [] with outcome
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast Finset.card_le_univ (edges outcome)

/-- Taking expectations preserves the necessary finite counting inequality. -/
theorem expected_boundary_card_le [Fintype Edge] [DecidableEq Vertex]
    (measure : Measure Ω) [IsFiniteMeasure measure]
    (edges : Ω → Finset Edge) (source : Ω → Edge → Vertex)
    (colour : Ω → Edge → Fin 4) (boundary : Ω → Vertex) (selected : Fin 4)
    (measurable_boundary : Measurable (fun outcome =>
      ((boundaryColourEdges (edges outcome) (source outcome) (colour outcome)
        (boundary outcome) selected).card : ℝ)))
    (measurable_total : Measurable (fun outcome =>
      ((colourEdges (edges outcome) (colour outcome) selected).card : ℝ))) :
    (∫ outcome, ((boundaryColourEdges (edges outcome) (source outcome) (colour outcome)
      (boundary outcome) selected).card : ℝ) ∂measure) ≤
      ∫ outcome, ((colourEdges (edges outcome) (colour outcome) selected).card : ℝ)
        ∂measure := by
  apply integral_mono
    (integrable_card measure _ measurable_boundary)
    (integrable_card measure _ measurable_total)
  intro outcome
  exact Nat.cast_le.mpr (boundaryColourEdges_card_le
    (edges outcome) (source outcome) (colour outcome) (boundary outcome) selected)

/-- The displayed green/red entries have the opposite strict inequality. -/
theorem displayed_green_red_incompatible {p : ℝ} (positive : 0 < p) (below_one : p < 1) :
    EM p 2 0 < EN p 4 0 := by
  change 2 * p ^ 2 < 2 * p
  have positive_product := mul_pos positive (sub_pos.mpr below_one)
  nlinarith

/-- In particular, the inconsistency occurs at the paper's critical parameter. -/
theorem critical_green_red_incompatible :
    EM Reduced.pc 2 0 < EN Reduced.pc 4 0 :=
  displayed_green_red_incompatible Reduced.pc_pos Reduced.pc_lt_one

/-- The excess at criticality is exactly `2 sqrt 5 - 4`, not a rounding effect. -/
theorem critical_green_red_difference :
    EN Reduced.pc 4 0 - EM Reduced.pc 2 0 = 2 * Real.sqrt 5 - 4 := by
  change 2 * Reduced.pc - 2 * Reduced.pc ^ 2 = 2 * Real.sqrt 5 - 4
  rw [Reduced.pc_sq]
  unfold Reduced.pc
  ring

/-- No finite random rule can simultaneously realize these two displayed entries. -/
theorem no_random_rule_realizes_displayed_green_red
    [Fintype Edge] [DecidableEq Vertex]
    (measure : Measure Ω) [IsFiniteMeasure measure]
    (edges : Ω → Finset Edge) (source : Ω → Edge → Vertex)
    (colour : Ω → Edge → Fin 4) (boundary : Ω → Vertex)
    (measurable_boundary : Measurable (fun outcome =>
      ((boundaryColourEdges (edges outcome) (source outcome) (colour outcome)
        (boundary outcome) 0).card : ℝ)))
    (measurable_total : Measurable (fun outcome =>
      ((colourEdges (edges outcome) (colour outcome) 0).card : ℝ)))
    {p : ℝ} (positive : 0 < p) (below_one : p < 1)
    (boundary_entry : (∫ outcome,
      ((boundaryColourEdges (edges outcome) (source outcome) (colour outcome)
        (boundary outcome) 0).card : ℝ) ∂measure) = EN p 4 0)
    (total_entry : (∫ outcome,
      ((colourEdges (edges outcome) (colour outcome) 0).card : ℝ) ∂measure) = EM p 2 0) :
    False := by
  have necessary_inequality := expected_boundary_card_le measure edges source colour boundary 0
    measurable_boundary measurable_total
  rw [boundary_entry, total_entry] at necessary_inequality
  exact (not_le_of_gt (displayed_green_red_incompatible positive below_one)) necessary_inequality

end Outlook
