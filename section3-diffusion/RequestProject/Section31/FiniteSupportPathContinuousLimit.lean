import RequestProject.Section31.FiniteSupportPathTightness
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Continuity of subsequential weak limits in the common uniform path space.
Finite-level step paths are allowed to be discontinuous. Closed tails of the
good supports retain their probability bounds under weak convergence, and
their intersection consists of continuous paths. The support and asymptotic
modulus hypotheses remain explicit generic inputs in this file. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter
open scoped UniformConvergence Topology Classical NNReal ENNReal

variable {Time State : Type*} [PseudoMetricSpace Time] [CompactSpace Time]
variable [MetricSpace State] [CompactSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]
variable (paths : (level : ℕ) → History level → Time → State)

/-- Open-set Portmanteau passes the eventual complement bound for a closed
tail to any weak limit along levels tending to infinity. -/
theorem finiteSupportModulusGoodHistory_weakLimit_tailClosure_compl_measure_le
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (finiteSupport : ∀ level, ∀ᵐ path ∂(laws level : Measure (FiniteSupportPathSpace paths)),
      path ∈ Set.range (finitePathEmbedding paths level))
    (thresholds : ℕ → ℕ) (windows errors : ℕ → ℝ) (budgets : ℕ → ℝ≥0∞)
    (modulusBound : ∀ index level, thresholds index ≤ level →
      (laws level : Measure (FiniteSupportPathSpace paths))
        (finiteSupportPathModulusSet paths (windows index) (errors index))ᶜ ≤ budgets index)
    (levels : ℕ → ℕ) (levelsTendsto : Tendsto levels atTop atTop)
    (limit : ProbabilityMeasure (FiniteSupportPathSpace paths))
    (weakConvergence : Tendsto (fun index => laws (levels index)) atTop (𝓝 limit))
    (threshold : ℕ) :
    (limit : Measure (FiniteSupportPathSpace paths)) (closure (finiteSupportGoodPathTail paths
      (finiteSupportModulusGoodHistory paths thresholds windows errors) threshold))ᶜ ≤
        ∑' index, budgets index := by
  apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto weakConvergence
    isClosed_closure.isOpen_compl).trans
  apply Filter.liminf_le_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [levelsTendsto.eventually (eventually_ge_atTop threshold)] with index levelLarge
  exact finiteSupportModulusGoodHistory_tailClosure_compl_measure_le paths laws finiteSupport
    thresholds windows errors budgets modulusBound threshold (levels index) levelLarge

/-- The closed tails decrease with their threshold. Continuity of measure
from below for their complements preserves a single bad-event budget when
all tails are intersected. -/
theorem finiteSupportModulusGoodHistory_weakLimit_tailIntersection_compl_measure_le
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (finiteSupport : ∀ level, ∀ᵐ path ∂(laws level : Measure (FiniteSupportPathSpace paths)),
      path ∈ Set.range (finitePathEmbedding paths level))
    (thresholds : ℕ → ℕ) (windows errors : ℕ → ℝ) (budgets : ℕ → ℝ≥0∞)
    (modulusBound : ∀ index level, thresholds index ≤ level →
      (laws level : Measure (FiniteSupportPathSpace paths))
        (finiteSupportPathModulusSet paths (windows index) (errors index))ᶜ ≤ budgets index)
    (levels : ℕ → ℕ) (levelsTendsto : Tendsto levels atTop atTop)
    (limit : ProbabilityMeasure (FiniteSupportPathSpace paths))
    (weakConvergence : Tendsto (fun index => laws (levels index)) atTop (𝓝 limit)) :
    (limit : Measure (FiniteSupportPathSpace paths)) (⋂ threshold, closure (finiteSupportGoodPathTail paths
      (finiteSupportModulusGoodHistory paths thresholds windows errors) threshold))ᶜ ≤
        ∑' index, budgets index := by
  have tailComplementsMonotone : Monotone (fun threshold : ℕ =>
      (closure (finiteSupportGoodPathTail paths
        (finiteSupportModulusGoodHistory paths thresholds windows errors) threshold))ᶜ) := by
    intro first second firstLeSecond
    apply Set.compl_subset_compl.mpr
    apply closure_mono
    rintro path ⟨level, levelLarge, membership⟩
    exact ⟨level, firstLeSecond.trans levelLarge, membership⟩
  rw [Set.compl_iInter, tailComplementsMonotone.measure_iUnion]
  exact iSup_le fun threshold =>
    finiteSupportModulusGoodHistory_weakLimit_tailClosure_compl_measure_le paths laws
      finiteSupport thresholds windows errors budgets modulusBound levels levelsTendsto limit
        weakConvergence threshold

/-- Asymptotic modulus control forces any weak limit along diverging levels
to give full outer measure to continuous paths. No measurability assumption
on the predicate `Continuous` is needed: its exceptional set has measure zero. -/
theorem finiteSupportPath_weakLimit_ae_continuous_of_asymptotic_modulus
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (finiteSupport : ∀ level, ∀ᵐ path ∂(laws level : Measure (FiniteSupportPathSpace paths)),
      path ∈ Set.range (finitePathEmbedding paths level))
    (asymptoticModulus : ∀ error > (0 : ℝ), ∀ probabilityTolerance : ℝ≥0∞,
      0 < probabilityTolerance → ∃ window > (0 : ℝ), ∃ threshold : ℕ,
        ∀ level ≥ threshold, (laws level : Measure (FiniteSupportPathSpace paths))
          (finiteSupportPathModulusSet paths window error)ᶜ ≤ probabilityTolerance)
    (levels : ℕ → ℕ) (levelsTendsto : Tendsto levels atTop atTop)
    (limit : ProbabilityMeasure (FiniteSupportPathSpace paths))
    (weakConvergence : Tendsto (fun index => laws (levels index)) atTop (𝓝 limit)) :
    ∀ᵐ path ∂(limit : Measure (FiniteSupportPathSpace paths)), Continuous (UniformFun.toFun path.val) := by
  classical
  obtain ⟨errors, _, errorsPositive, errorsVanish⟩ :
      ∃ errors : ℕ → ℝ, StrictAnti errors ∧ (∀ index, 0 < errors index) ∧
        Tendsto errors atTop (𝓝 0) := exists_seq_strictAnti_tendsto (0 : ℝ)
  apply ae_iff.mpr
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro tolerance tolerancePositive _
  have modulusChoice : ∀ index : ℕ, ∃ window > (0 : ℝ), ∃ threshold : ℕ,
      ∀ level ≥ threshold, (laws level : Measure (FiniteSupportPathSpace paths))
        (finiteSupportPathModulusSet paths window (errors index))ᶜ ≤
          (tolerance : ℝ≥0∞) * 2 ^ (-1 - (index : ℤ)) := by
    intro index
    apply asymptoticModulus (errors index) (errorsPositive index)
    exact ENNReal.mul_pos_iff.mpr
      ⟨ENNReal.coe_pos.mpr tolerancePositive, ENNReal.zpow_pos (by norm_num) (by norm_num) _⟩
  choose windows windowsPositive thresholds modulusBound using modulusChoice
  calc
    (limit : Measure (FiniteSupportPathSpace paths)) {path | ¬ Continuous (UniformFun.toFun path.val)} ≤
        (limit : Measure (FiniteSupportPathSpace paths)) (⋂ threshold, closure (finiteSupportGoodPathTail paths
          (finiteSupportModulusGoodHistory paths thresholds windows errors) threshold))ᶜ := by
      apply measure_mono
      intro path notContinuous membership
      exact notContinuous (finiteSupportModulusGoodHistory_tailIntersection_continuous paths
        thresholds windows errors windowsPositive errorsVanish path membership)
    _ ≤ ∑' index : ℕ, (tolerance : ℝ≥0∞) * 2 ^ (-1 - (index : ℤ)) :=
      finiteSupportModulusGoodHistory_weakLimit_tailIntersection_compl_measure_le paths laws
        finiteSupport thresholds windows errors
          (fun index => (tolerance : ℝ≥0∞) * 2 ^ (-1 - (index : ℤ))) modulusBound
            levels levelsTendsto limit weakConvergence
    _ = 0 + (tolerance : ℝ≥0∞) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_two_zpow_neg_add_one, mul_one, zero_add]

/-- The real-valued native probability estimates are enough to apply the
generic continuous weak-limit theorem. -/
theorem finiteSupportPath_weakLimit_ae_continuous_of_asymptotic_modulus_toReal
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (finiteSupport : ∀ level, ∀ᵐ path ∂(laws level : Measure (FiniteSupportPathSpace paths)),
      path ∈ Set.range (finitePathEmbedding paths level))
    (asymptoticModulus : ∀ error > (0 : ℝ), ∀ probabilityTolerance > (0 : ℝ),
      ∃ window > (0 : ℝ), ∃ threshold : ℕ,
        ∀ level ≥ threshold, ((laws level : Measure (FiniteSupportPathSpace paths))
          (finiteSupportPathModulusSet paths window error)ᶜ).toReal ≤ probabilityTolerance)
    (levels : ℕ → ℕ) (levelsTendsto : Tendsto levels atTop atTop)
    (limit : ProbabilityMeasure (FiniteSupportPathSpace paths))
    (weakConvergence : Tendsto (fun index => laws (levels index)) atTop (𝓝 limit)) :
    ∀ᵐ path ∂(limit : Measure (FiniteSupportPathSpace paths)), Continuous (UniformFun.toFun path.val) := by
  apply finiteSupportPath_weakLimit_ae_continuous_of_asymptotic_modulus paths laws finiteSupport
    ?_ levels levelsTendsto limit weakConvergence
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

#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportModulusGoodHistory_weakLimit_tailClosure_compl_measure_le
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportModulusGoodHistory_weakLimit_tailIntersection_compl_measure_le
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPath_weakLimit_ae_continuous_of_asymptotic_modulus
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPath_weakLimit_ae_continuous_of_asymptotic_modulus_toReal
