import RequestProject.Section31.QuadraticEnergySemigroupScalarAnalytic
import RequestProject.Section31.QuadraticEnergySemigroupInjective
import RequestProject.Section31.PositiveL2SemigroupZeroInterval
import RequestProject.Section31.ProbabilityL2SemigroupMixing
import RequestProject.Section31.QuadraticEnergySemigroupMarkov
import Mathlib.Analysis.Analytic.Uniqueness

/-! Strict positivity of correlations of nonzero nonnegative inputs for the
constructed closed semigroup on a probability space. Normal contractions and a
Poincaré bound imply this through the proved semigroup injectivity, support
inclusion, scalar time analyticity, and mixing estimate. None of these target
properties is assumed. The actual Xi consumer fills both form conditions.
Candidate source, awaiting whole-file compilation. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

variable {Space : Type*} [MeasurableSpace Space] (law : Measure Space) [IsProbabilityMeasure law]

theorem probability_L2_integral_pos_of_nonnegative_nonzero (values : Lp ℝ 2 law)
    (nonnegative : ∀ᵐ point ∂law, 0 ≤ values point) (nonzero : values ≠ 0) :
    0 < ∫ point, values point ∂law := by
  have integrableValues : Integrable values law :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp values)
  have integralNonnegative : 0 ≤ ∫ point, values point ∂law := integral_nonneg_of_ae nonnegative
  apply lt_of_le_of_ne integralNonnegative
  intro zero
  have zeroAE := (integral_eq_zero_iff_of_nonneg_ae nonnegative integrableValues).mp zero.symm
  apply nonzero
  apply Lp.ext
  exact zeroAE.trans (Lp.coeFn_zero ℝ 2 law).symm

namespace QuadraticEnergySpace

theorem closedSemigroup_positive_correlation
    (domain : Submodule ℝ (Lp ℝ 2 law)) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set (Lp ℝ 2 law)))
    (normalContractions : ∀ (contraction : ℝ → ℝ)
      (lipschitz : LipschitzWith 1 contraction) (zero : contraction 0 = 0)
      (target : closedDomain domain form nonnegative),
      ∃ membership : lipschitz.compLp zero target.val ∈ closedDomain domain form nonnegative,
        closedForm domain form nonnegative closable ⟨lipschitz.compLp zero target.val, membership⟩ ≤
          closedForm domain form nonnegative closable target)
    (constant : ℝ) (constantNonnegative : 0 ≤ constant)
    (varianceBound : ∀ target : closedDomain domain form nonnegative,
      (∫ point, (target.val point - ∫ other, target.val other ∂law) ^ 2 ∂law) ≤
        constant * closedForm domain form nonnegative closable target)
    (one : domain) (oneEnergy : form one = 0)
    (oneAE : ∀ᵐ point ∂law, (one : Lp ℝ 2 law) point = 1)
    (first second : Lp ℝ 2 law)
    (firstNonnegative : ∀ᵐ point ∂law, 0 ≤ first point)
    (secondNonnegative : ∀ᵐ point ∂law, 0 ≤ second point)
    (firstNonzero : first ≠ 0) (secondNonzero : second ≠ 0)
    (time : ℝ≥0) (timePositive : 0 < time) :
    0 < inner ℝ first (closedSemigroup domain form nonnegative closable domainDense time second) := by
  have positivity (parameter : ℝ≥0) (values : Lp ℝ 2 law)
      (valuesNonnegative : ∀ᵐ point ∂law, 0 ≤ values point) :
      ∀ᵐ point ∂law, 0 ≤ closedSemigroup domain form nonnegative closable domainDense parameter values point :=
    lp_closedSemigroup_preserves_nonnegative law domain form nonnegative closable domainDense
      normalContractions parameter values valuesNonnegative
  have correlationNonnegative := L2_inner_nonnegative_of_ae_nonnegative law first
    (closedSemigroup domain form nonnegative closable domainDense time second)
    firstNonnegative (positivity time second secondNonnegative)
  by_contra notPositive
  have correlationZero : inner ℝ first (closedSemigroup domain form nonnegative closable domainDense time second) = 0 :=
    le_antisymm (not_lt.mp notPositive) correlationNonnegative
  have timeRealPositive : 0 < (time : ℝ) := timePositive
  have zeroNeighborhood : (fun parameter : ℝ => inner ℝ first
      (closedSemigroup domain form nonnegative closable domainDense parameter.toNNReal second)) =ᶠ[𝓝 ((time : ℝ) / 2)] 0 := by
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < (time : ℝ) / 2 by linarith)
      (show (time : ℝ) / 2 < (time : ℝ) by linarith)] with parameter bounds
    have parameterAtMost : parameter.toNNReal ≤ time := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ bounds.1.le]
      exact bounds.2.le
    exact positive_L2_semigroup_zero_correlation_of_le law
      (closedSemigroup domain form nonnegative closable domainDense)
      (closedSemigroup_add domain form nonnegative closable domainDense) positivity
      (closedSemigroup_pairing_pos domain form nonnegative closable domainDense)
      first second firstNonnegative secondNonnegative parameter.toNNReal time parameterAtMost correlationZero
  have zeroEverywhere := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (closedSemigroup_scalar_analyticOnNhd domain form nonnegative closable domainDense first second)
    isPreconnected_Ioi
      (show (time : ℝ) / 2 ∈ Set.Ioi (0 : ℝ) from div_pos timeRealPositive (by norm_num)) zeroNeighborhood
  have zeroSequence (index : ℕ) : inner ℝ first
      (closedSemigroup domain form nonnegative closable domainDense (index + 1) second) = 0 := by
    have identity := zeroEverywhere
      (show (((index : ℝ≥0) + 1 : ℝ≥0) : ℝ) ∈ Set.Ioi (0 : ℝ) by
        change (0 : ℝ) < (index : ℝ) + 1
        positivity)
    simpa only [Real.toNNReal_coe, Pi.zero_apply] using identity
  have scalarLimit := (innerSL ℝ first).continuous.continuousAt.tendsto.comp
    (closedSemigroup_tendsto_mean law domain form nonnegative closable domainDense constant
      constantNonnegative varianceBound one oneEnergy oneAE second)
  change Tendsto (fun index : ℕ => inner ℝ first
      (closedSemigroup domain form nonnegative closable domainDense (index + 1) second)) atTop
    (𝓝 (inner ℝ first ((∫ point, second point ∂law) • Lp.const 2 law (1 : ℝ)))) at scalarLimit
  have zeroLimit : Tendsto (fun index : ℕ => inner ℝ first
      (closedSemigroup domain form nonnegative closable domainDense (index + 1) second)) atTop (𝓝 0) := by
    simpa only [zeroSequence] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have meanPairingPositive : 0 < inner ℝ first ((∫ point, second point ∂law) • Lp.const 2 law (1 : ℝ)) := by
    rw [inner_smul_right, ← real_inner_comm first (Lp.const 2 law (1 : ℝ)), L2_inner_one_eq_integral law first]
    exact mul_pos
      (probability_L2_integral_pos_of_nonnegative_nonzero law second secondNonnegative secondNonzero)
      (probability_L2_integral_pos_of_nonnegative_nonzero law first firstNonnegative firstNonzero)
  exact (ne_of_gt meanPairingPositive) (tendsto_nhds_unique scalarLimit zeroLimit)

end QuadraticEnergySpace
end IGS.Sec31

#print axioms IGS.Sec31.probability_L2_integral_pos_of_nonnegative_nonzero
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_positive_correlation
