import RequestProject.Section31.VaryingEmbeddedL2Core
import Mathlib.MeasureTheory.Function.Holder

/-! Bounded multiplication preserves genuine varying-space strong convergence.
The operators are constructed from the actual bounded measurable functions.
Compatibility with restrictions is proved using their AE representatives. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal

namespace VaryingHilbertCore

variable {Core Hilbert : Type*} [AddCommGroup Core] [Module ℝ Core]
    [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    {LevelHilbert : ℕ → Type*}
    [∀ level, NormedAddCommGroup (LevelHilbert level)]
    [∀ level, InnerProductSpace ℝ (LevelHilbert level)]

theorem strong_compatible_bounded_operators
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (operators : ∀ level, LevelHilbert level →L[ℝ] LevelHilbert level)
    (operator : Hilbert →L[ℝ] Hilbert) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (operatorBounds : ∀ level, ‖operators level‖ ≤ bound) (operatorBound : ‖operator‖ ≤ bound)
    (transform : Core → Core)
    (levelCompatible : ∀ level element,
      operators level (core.restrict level element) = core.restrict level (transform element))
    (limitCompatible : ∀ element, operator (core.embed element) = core.embed (transform element))
    {sequence : ∀ level, LevelHilbert level} {limit : Hilbert}
    (convergence : core.Strong sequence limit) :
    core.Strong (fun level => operators level (sequence level)) (operator limit) := by
  intro tolerance positive
  have denominatorPositive : 0 < bound + 1 := by linarith
  have approximationPositive : 0 < tolerance / (bound + 1) := div_pos positive denominatorPositive
  obtain ⟨element, limitClose, levelClose⟩ := convergence _ approximationPositive
  have scaled : (bound + 1) * (tolerance / (bound + 1)) = tolerance :=
    mul_div_cancel₀ _ denominatorPositive.ne'
  have scaledStrict : bound * (tolerance / (bound + 1)) < tolerance := by nlinarith
  refine ⟨transform element, ?_, ?_⟩
  · rw [← limitCompatible, ← map_sub]
    exact ((operator.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right operatorBound (norm_nonneg _))).trans_lt
      ((mul_le_mul_of_nonneg_left limitClose.le boundNonnegative).trans_lt scaledStrict)
  · filter_upwards [levelClose] with level close
    rw [← levelCompatible, ← map_sub]
    exact (((operators level).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (operatorBounds level) (norm_nonneg _))).trans_lt
      ((mul_le_mul_of_nonneg_left close.le boundNonnegative).trans_lt scaledStrict)

end VaryingHilbertCore

namespace BoundedL2Multiplication

variable {X : Type*} [MeasurableSpace X]

noncomputable def coefficient (measure : Measure X) (multiplier : X → ℝ)
    (measurable : AEStronglyMeasurable multiplier measure) (bound : ℝ)
    (bounded : ∀ᵐ point ∂measure, ‖multiplier point‖ ≤ bound) : Lp ℝ ∞ measure :=
  (memLp_top_of_bound measurable bound bounded).toLp multiplier

theorem coefficient_norm_le (measure : Measure X) (multiplier : X → ℝ)
    (measurable : AEStronglyMeasurable multiplier measure) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ᵐ point ∂measure, ‖multiplier point‖ ≤ bound) :
    ‖coefficient measure multiplier measurable bound bounded‖ ≤ bound := by
  rw [coefficient, Lp.norm_toLp, eLpNorm_exponent_top]
  exact (ENNReal.toReal_mono (by finiteness) (eLpNormEssSup_le_of_ae_bound bounded)).trans
    (le_of_eq (ENNReal.toReal_ofReal boundNonnegative))

noncomputable def operator (measure : Measure X) (multiplier : X → ℝ)
    (measurable : AEStronglyMeasurable multiplier measure) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ᵐ point ∂measure, ‖multiplier point‖ ≤ bound) :
    Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure :=
  ({ toFun := fun values => coefficient measure multiplier measurable bound bounded • values
     map_add' := fun first second => Lp.add_smul _ first second
     map_smul' := fun scalar values => (Lp.smul_comm scalar
       (coefficient measure multiplier measurable bound bounded) values).symm } :
    Lp ℝ 2 measure →ₗ[ℝ] Lp ℝ 2 measure).mkContinuous bound (by
      intro values
      exact (Lp.norm_smul_le _ values).trans
        (mul_le_mul_of_nonneg_right
          (coefficient_norm_le measure multiplier measurable bound boundNonnegative bounded)
          (norm_nonneg values)))

theorem operator_norm_le (measure : Measure X) (multiplier : X → ℝ)
    (measurable : AEStronglyMeasurable multiplier measure) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ᵐ point ∂measure, ‖multiplier point‖ ≤ bound) :
    ‖operator measure multiplier measurable bound boundNonnegative bounded‖ ≤ bound :=
  LinearMap.mkContinuous_norm_le _ boundNonnegative _

theorem operator_ae (measure : Measure X) (multiplier : X → ℝ)
    (measurable : AEStronglyMeasurable multiplier measure) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ᵐ point ∂measure, ‖multiplier point‖ ≤ bound)
    (values : Lp ℝ 2 measure) :
    (operator measure multiplier measurable bound boundNonnegative bounded values : X → ℝ)
      =ᵐ[measure] fun point => multiplier point * values point := by
  have coefficientAE : (coefficient measure multiplier measurable bound bounded : X → ℝ)
      =ᵐ[measure] multiplier := MemLp.coeFn_toLp _
  filter_upwards [Lp.coeFn_lpSMul (r := 2)
      (coefficient measure multiplier measurable bound bounded) values, coefficientAE]
    with point multiplicationEvaluation coefficientEvaluation
  simpa only [Pi.smul_apply', Pi.mul_apply, smul_eq_mul, coefficientEvaluation] using multiplicationEvaluation

end BoundedL2Multiplication

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    {LevelSpace : ℕ → Type*} [∀ level, MeasurableSpace (LevelSpace level)]
    (measures : ∀ level, ProbabilityMeasure (LevelSpace level))
    (embeddings : ∀ level, LevelSpace level → Space)
    (measurableEmbeddings : ∀ level, Measurable (embeddings level))
    (measure : ProbabilityMeasure Space)
    (weakConvergence : Tendsto
      (embeddedProbabilityMeasures measures embeddings measurableEmbeddings) atTop (nhds measure))

theorem embeddedProbabilityL2Core_restrict_ae (level : ℕ) (test : Space →ᵇ ℝ) :
    ((embeddedProbabilityL2Core measures embeddings measurableEmbeddings measure weakConvergence).restrict
      level test : LevelSpace level → ℝ) =ᵐ[(measures level : Measure (LevelSpace level))]
      fun point => test (embeddings level point) := by
  let preserving := embeddingMeasurePreserving measures embeddings measurableEmbeddings level
  have representative := BoundedContinuousFunction.coeFn_toLp (𝕜 := ℝ) 2
    (embeddedProbabilityMeasures measures embeddings measurableEmbeddings level : Measure Space) test
  exact (Lp.coeFn_compMeasurePreserving _ preserving).trans
    (preserving.quasiMeasurePreserving.ae_eq representative)

noncomputable def boundedContinuousLimitMultiplication (multiplier : Space →ᵇ ℝ) :
    Lp ℝ 2 (measure : Measure Space) →L[ℝ] Lp ℝ 2 (measure : Measure Space) :=
  BoundedL2Multiplication.operator (measure : Measure Space) multiplier
    multiplier.continuous.measurable.aestronglyMeasurable ‖multiplier‖ (norm_nonneg _)
    (Eventually.of_forall multiplier.norm_coe_le_norm)

noncomputable def boundedContinuousLevelMultiplication (multiplier : Space →ᵇ ℝ) (level : ℕ) :
    Lp ℝ 2 (measures level : Measure (LevelSpace level)) →L[ℝ]
      Lp ℝ 2 (measures level : Measure (LevelSpace level)) :=
  BoundedL2Multiplication.operator (measures level : Measure (LevelSpace level))
    (fun point => multiplier (embeddings level point))
    (multiplier.continuous.measurable.comp (measurableEmbeddings level)).aestronglyMeasurable
    ‖multiplier‖ (norm_nonneg _)
    (Eventually.of_forall fun point => multiplier.norm_coe_le_norm (embeddings level point))

theorem embeddedProbabilityL2Core_strong_multiplication
    (multiplier : Space →ᵇ ℝ)
    {sequence : ∀ level, Lp ℝ 2 (measures level : Measure (LevelSpace level))}
    {limit : Lp ℝ 2 (measure : Measure Space)}
    (convergence : (embeddedProbabilityL2Core measures embeddings measurableEmbeddings measure weakConvergence).Strong
      sequence limit) :
    (embeddedProbabilityL2Core measures embeddings measurableEmbeddings measure weakConvergence).Strong
      (fun level => boundedContinuousLevelMultiplication measures embeddings measurableEmbeddings multiplier level
        (sequence level)) (boundedContinuousLimitMultiplication measure multiplier limit) := by
  apply VaryingHilbertCore.strong_compatible_bounded_operators _ _ _ ‖multiplier‖
    (norm_nonneg _) _ _ (fun test => multiplier * test) _ _ convergence
  · intro level
    exact BoundedL2Multiplication.operator_norm_le _ _ _ _ _ _
  · exact BoundedL2Multiplication.operator_norm_le _ _ _ _ _ _
  · intro level test
    apply Lp.ext
    filter_upwards [BoundedL2Multiplication.operator_ae
        (measures level : Measure (LevelSpace level))
        (fun point => multiplier (embeddings level point))
        (multiplier.continuous.measurable.comp (measurableEmbeddings level)).aestronglyMeasurable
        ‖multiplier‖ (norm_nonneg _)
        (Eventually.of_forall fun point => multiplier.norm_coe_le_norm (embeddings level point))
        ((embeddedProbabilityL2Core measures embeddings measurableEmbeddings measure weakConvergence).restrict level test),
      embeddedProbabilityL2Core_restrict_ae measures embeddings measurableEmbeddings measure weakConvergence level test,
      embeddedProbabilityL2Core_restrict_ae measures embeddings measurableEmbeddings measure weakConvergence level (multiplier * test)]
      with point multiplicationEvaluation testEvaluation productEvaluation
    simpa only [boundedContinuousLevelMultiplication, multiplicationEvaluation, testEvaluation, productEvaluation,
      BoundedContinuousFunction.mul_apply]
  · intro test
    change boundedContinuousLimitMultiplication measure multiplier
      (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ test) =
      BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ (multiplier * test)
    apply Lp.ext
    filter_upwards [BoundedL2Multiplication.operator_ae (measure : Measure Space) multiplier
        multiplier.continuous.measurable.aestronglyMeasurable ‖multiplier‖ (norm_nonneg _)
        (Eventually.of_forall multiplier.norm_coe_le_norm)
        (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ test),
      BoundedContinuousFunction.coeFn_toLp (𝕜 := ℝ) 2 (measure : Measure Space) test,
      BoundedContinuousFunction.coeFn_toLp (𝕜 := ℝ) 2 (measure : Measure Space) (multiplier * test)]
      with point multiplicationEvaluation testEvaluation productEvaluation
    simpa only [boundedContinuousLimitMultiplication, multiplicationEvaluation, testEvaluation, productEvaluation,
      BoundedContinuousFunction.mul_apply]

end IGS.Sec31

#print axioms IGS.Sec31.VaryingHilbertCore.strong_compatible_bounded_operators
#print axioms IGS.Sec31.BoundedL2Multiplication.operator_norm_le
#print axioms IGS.Sec31.BoundedL2Multiplication.operator_ae
#print axioms IGS.Sec31.embeddedProbabilityL2Core_restrict_ae
#print axioms IGS.Sec31.embeddedProbabilityL2Core_strong_multiplication
