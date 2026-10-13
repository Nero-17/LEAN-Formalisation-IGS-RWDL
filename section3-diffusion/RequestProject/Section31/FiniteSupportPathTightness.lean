import RequestProject.Section31.FiniteSupportPathCompactness
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! A probability tightness consumer for the common uniform path space.
The two premises are genuine finite-level support and asymptotic modulus
control. They are explicit generic inputs, to be filled by the actual
floor-path laws; this file does not assume or assert their native validity. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter
open scoped UniformConvergence Topology Classical NNReal ENNReal

variable {Time State : Type*} [PseudoMetricSpace Time] [CompactSpace Time]
variable [MetricSpace State] [CompactSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]
variable (paths : (level : ℕ) → History level → Time → State)

theorem finiteSupportModulusGoodHistory_image_compl_measure_le
    (law : Measure (FiniteSupportPathSpace paths)) (level : ℕ)
    (finiteSupport : ∀ᵐ path ∂law,
      path ∈ Set.range (finitePathEmbedding paths level))
    (thresholds : ℕ → ℕ) (windows errors : ℕ → ℝ) (budgets : ℕ → ℝ≥0∞)
    (modulusBound : ∀ index, thresholds index ≤ level →
      law (finiteSupportPathModulusSet paths (windows index) (errors index))ᶜ ≤ budgets index) :
    law (finitePathEmbedding paths level ''
      finiteSupportModulusGoodHistory paths thresholds windows errors level)ᶜ ≤
        ∑' index, budgets index := by
  let bad (index : ℕ) : Set (FiniteSupportPathSpace paths) :=
    {path | thresholds index ≤ level ∧
      path ∈ (finiteSupportPathModulusSet paths (windows index) (errors index))ᶜ}
  have imageFailure : law (finitePathEmbedding paths level ''
      finiteSupportModulusGoodHistory paths thresholds windows errors level)ᶜ ≤
        law (⋃ index, bad index) := by
    apply measure_mono_ae
    filter_upwards [finiteSupport] with path pathSupport
    intro notGood
    obtain ⟨history, rfl⟩ := pathSupport
    by_contra noFailure
    apply notGood
    refine ⟨history, ?_, rfl⟩
    intro index enabled
    by_contra failed
    exact noFailure (Set.mem_iUnion.mpr ⟨index, enabled, failed⟩)
  calc
    law (finitePathEmbedding paths level ''
        finiteSupportModulusGoodHistory paths thresholds windows errors level)ᶜ ≤
      law (⋃ index, bad index) := imageFailure
    _ ≤ ∑' index, law (bad index) := measure_iUnion_le _
    _ ≤ ∑' index, budgets index := by
      apply ENNReal.tsum_le_tsum
      intro index
      by_cases enabled : thresholds index ≤ level
      · exact (measure_mono (show bad index ⊆
          (finiteSupportPathModulusSet paths (windows index) (errors index))ᶜ from
            fun _ membership => membership.2)).trans (modulusBound index enabled)
      · have empty : bad index = ∅ := by
          ext path
          simp only [bad, Set.mem_setOf_eq, enabled, false_and, Set.mem_empty_iff_false]
        rw [empty, measure_empty]
        exact bot_le

theorem finiteSupportModulusGoodHistory_compact_compl_measure_le
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (finiteSupport : ∀ level, ∀ᵐ path ∂(laws level : Measure (FiniteSupportPathSpace paths)),
      path ∈ Set.range (finitePathEmbedding paths level))
    (thresholds : ℕ → ℕ) (windows errors : ℕ → ℝ) (budgets : ℕ → ℝ≥0∞)
    (modulusBound : ∀ index level, thresholds index ≤ level →
      (laws level : Measure (FiniteSupportPathSpace paths))
        (finiteSupportPathModulusSet paths (windows index) (errors index))ᶜ ≤ budgets index)
    (level : ℕ) :
    (laws level : Measure (FiniteSupportPathSpace paths)) (closure (finiteSupportGoodPathUnion paths
      (finiteSupportModulusGoodHistory paths thresholds windows errors)))ᶜ ≤
        ∑' index, budgets index := by
  apply le_trans (measure_mono ?_)
    (finiteSupportModulusGoodHistory_image_compl_measure_le paths (laws level : Measure (FiniteSupportPathSpace paths))
      level (finiteSupport level) thresholds windows errors budgets
        (fun index enabled => modulusBound index level enabled))
  apply Set.compl_subset_compl.mpr
  intro path membership
  exact subset_closure (Set.mem_iUnion.mpr ⟨level, membership⟩)

/-- A countable ladder of asymptotic modulus bounds gives a common compact
capture set. Only the bounds enabled at the current level enter its good
histories; the finitely many early supports remain inside the compact set. -/
theorem finiteSupportModulusGoodHistory_exists_compact_capture
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (finiteSupport : ∀ level, ∀ᵐ path ∂(laws level : Measure (FiniteSupportPathSpace paths)),
      path ∈ Set.range (finitePathEmbedding paths level))
    (thresholds : ℕ → ℕ) (windows errors : ℕ → ℝ) (budgets : ℕ → ℝ≥0∞)
    (windowsPositive : ∀ index, 0 < windows index)
    (errorsVanish : Tendsto errors atTop (𝓝 0))
    (modulusBound : ∀ index level, thresholds index ≤ level →
      (laws level : Measure (FiniteSupportPathSpace paths))
        (finiteSupportPathModulusSet paths (windows index) (errors index))ᶜ ≤ budgets index) :
    ∃ compact : Set (FiniteSupportPathSpace paths), IsCompact compact ∧
      ∀ level, (laws level : Measure (FiniteSupportPathSpace paths)) compactᶜ ≤ ∑' index, budgets index := by
  refine ⟨closure (finiteSupportGoodPathUnion paths
    (finiteSupportModulusGoodHistory paths thresholds windows errors)),
      finiteSupportModulusGoodHistory_union_isCompact_closure paths thresholds windows errors
        windowsPositive errorsVanish, ?_⟩
  exact finiteSupportModulusGoodHistory_compact_compl_measure_le paths laws finiteSupport
    thresholds windows errors budgets modulusBound

/-- The same bad-event budget controls each closed tail for every law whose
level belongs to that tail. This is the closed-set input needed for a
subsequential weak-limit support argument. -/
theorem finiteSupportModulusGoodHistory_tailClosure_compl_measure_le
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (finiteSupport : ∀ level, ∀ᵐ path ∂(laws level : Measure (FiniteSupportPathSpace paths)),
      path ∈ Set.range (finitePathEmbedding paths level))
    (thresholds : ℕ → ℕ) (windows errors : ℕ → ℝ) (budgets : ℕ → ℝ≥0∞)
    (modulusBound : ∀ index level, thresholds index ≤ level →
      (laws level : Measure (FiniteSupportPathSpace paths))
        (finiteSupportPathModulusSet paths (windows index) (errors index))ᶜ ≤ budgets index)
    (threshold level : ℕ) (levelLarge : threshold ≤ level) :
    (laws level : Measure (FiniteSupportPathSpace paths)) (closure (finiteSupportGoodPathTail paths
      (finiteSupportModulusGoodHistory paths thresholds windows errors) threshold))ᶜ ≤
        ∑' index, budgets index := by
  apply le_trans (measure_mono ?_)
    (finiteSupportModulusGoodHistory_image_compl_measure_le paths (laws level : Measure (FiniteSupportPathSpace paths))
      level (finiteSupport level) thresholds windows errors budgets
        (fun index enabled => modulusBound index level enabled))
  apply Set.compl_subset_compl.mpr
  intro path membership
  exact subset_closure ⟨level, levelLarge, membership⟩

/-- The generic probability tightness consumer. Its asymptotic modulus
premise is to be proved from the actual transition rules in the native
application; it is not a premise asserting tightness itself. -/
theorem finiteSupportPath_isTightMeasureSet_of_asymptotic_modulus
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (finiteSupport : ∀ level, ∀ᵐ path ∂(laws level : Measure (FiniteSupportPathSpace paths)),
      path ∈ Set.range (finitePathEmbedding paths level))
    (asymptoticModulus : ∀ error > (0 : ℝ), ∀ probabilityTolerance : ℝ≥0∞,
      0 < probabilityTolerance → ∃ window > (0 : ℝ), ∃ threshold : ℕ,
        ∀ level ≥ threshold, (laws level : Measure (FiniteSupportPathSpace paths))
          (finiteSupportPathModulusSet paths window error)ᶜ ≤ probabilityTolerance) :
    IsTightMeasureSet (Set.range (fun level => (laws level : Measure (FiniteSupportPathSpace paths)))) := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro tolerance tolerancePositive
  obtain ⟨errors, _, errorsPositive, errorsVanish⟩ :
      ∃ errors : ℕ → ℝ, StrictAnti errors ∧ (∀ index, 0 < errors index) ∧
        Tendsto errors atTop (𝓝 0) := exists_seq_strictAnti_tendsto (0 : ℝ)
  have modulusChoice : ∀ index : ℕ, ∃ window > (0 : ℝ), ∃ threshold : ℕ,
      ∀ level ≥ threshold, (laws level : Measure (FiniteSupportPathSpace paths))
        (finiteSupportPathModulusSet paths window (errors index))ᶜ ≤
          tolerance * 2 ^ (-1 - (index : ℤ)) := by
    intro index
    apply asymptoticModulus (errors index) (errorsPositive index)
    exact ENNReal.mul_pos_iff.mpr
      ⟨tolerancePositive, ENNReal.zpow_pos (by norm_num) (by norm_num) _⟩
  choose windows windowsPositive thresholds modulusBound using modulusChoice
  obtain ⟨compact, compactIsCompact, compactBound⟩ :=
    finiteSupportModulusGoodHistory_exists_compact_capture paths laws finiteSupport
      thresholds windows errors (fun index => tolerance * 2 ^ (-1 - (index : ℤ)))
        windowsPositive errorsVanish modulusBound
  refine ⟨compact, compactIsCompact, ?_⟩
  rintro law ⟨level, rfl⟩
  calc
    (laws level : Measure (FiniteSupportPathSpace paths)) compactᶜ ≤
        ∑' index : ℕ, tolerance * 2 ^ (-1 - (index : ℤ)) := compactBound level
    _ = tolerance := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_two_zpow_neg_add_one, mul_one]

/-- Real-valued bad-event estimates, as supplied by the finite path-law
estimates, suffice for the generic tightness consumer. -/
theorem finiteSupportPath_isTightMeasureSet_of_asymptotic_modulus_toReal
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (finiteSupport : ∀ level, ∀ᵐ path ∂(laws level : Measure (FiniteSupportPathSpace paths)),
      path ∈ Set.range (finitePathEmbedding paths level))
    (asymptoticModulus : ∀ error > (0 : ℝ), ∀ probabilityTolerance > (0 : ℝ),
      ∃ window > (0 : ℝ), ∃ threshold : ℕ,
        ∀ level ≥ threshold, ((laws level : Measure (FiniteSupportPathSpace paths))
          (finiteSupportPathModulusSet paths window error)ᶜ).toReal ≤ probabilityTolerance) :
    IsTightMeasureSet (Set.range (fun level => (laws level : Measure (FiniteSupportPathSpace paths)))) := by
  apply finiteSupportPath_isTightMeasureSet_of_asymptotic_modulus paths laws finiteSupport
  intro error errorPositive probabilityTolerance probabilityPositive
  by_cases probabilityInfinite : probabilityTolerance = ∞
  · refine ⟨1, by norm_num, 0, ?_⟩
    intro level _
    rw [probabilityInfinite]
    exact le_top
  · obtain ⟨window, windowPositive, threshold, modulusBound⟩ :=
      asymptoticModulus error errorPositive probabilityTolerance.toReal
        (ENNReal.toReal_pos probabilityPositive.ne' probabilityInfinite)
    refine ⟨window, windowPositive, threshold, ?_⟩
    intro level levelLarge
    calc
      (laws level : Measure (FiniteSupportPathSpace paths)) (finiteSupportPathModulusSet paths window error)ᶜ =
          ENNReal.ofReal (((laws level : Measure (FiniteSupportPathSpace paths))
            (finiteSupportPathModulusSet paths window error)ᶜ).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal probabilityTolerance.toReal :=
        ENNReal.ofReal_le_ofReal (modulusBound level levelLarge)
      _ = probabilityTolerance := ENNReal.ofReal_toReal probabilityInfinite

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportModulusGoodHistory_image_compl_measure_le
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportModulusGoodHistory_compact_compl_measure_le
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportModulusGoodHistory_exists_compact_capture
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportModulusGoodHistory_tailClosure_compl_measure_le
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPath_isTightMeasureSet_of_asymptotic_modulus
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPath_isTightMeasureSet_of_asymptotic_modulus_toReal
