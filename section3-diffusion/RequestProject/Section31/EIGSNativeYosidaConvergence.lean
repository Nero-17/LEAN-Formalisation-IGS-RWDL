import RequestProject.Section31.EIGSNativeResolventConvergence
import RequestProject.Section31.QuadraticEnergyYosidaSemigroup
import Mathlib.Algebra.BigOperators.Intervals

/-! Fixed-step actual Yosida exponential convergence in genuine varying Hilbert
spaces. Finite powers and polynomials preserve Strong convergence, and an
explicit scalar exponential tail controls the actual operator power series
uniformly. No Trotter or semigroup-convergence theorem is an input. -/

namespace IGS.Sec31

open Filter Topology
open scoped BigOperators

set_option maxHeartbeats 4000000

noncomputable local instance {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] :
    NormedAlgebra ℚ (Space →L[ℝ] Space) :=
  NormedAlgebra.restrictScalars ℚ ℝ (Space →L[ℝ] Space)

namespace VaryingBoundedExponential

noncomputable def polynomial {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (operator : Space →L[ℝ] Space) (depth : ℕ) : Space →L[ℝ] Space :=
  ∑ index ∈ Finset.range depth, (index.factorial : ℝ)⁻¹ • operator ^ index

noncomputable def scalarTail (bound : ℝ) (depth : ℕ) : ℝ :=
  Real.exp bound - ∑ index ∈ Finset.range depth, (index.factorial : ℝ)⁻¹ * bound ^ index

theorem scalarTail_tendsto (bound : ℝ) :
    Tendsto (scalarTail bound) atTop (nhds 0) := by
  have scalarSum : HasSum (fun index : ℕ => (index.factorial : ℝ)⁻¹ * bound ^ index) (Real.exp bound) := by
    simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) bound
  simpa only [scalarTail, sub_self] using
    (tendsto_const_nhds (x := Real.exp bound)).sub scalarSum.tendsto_sum_nat

theorem norm_exp_sub_polynomial_le
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
    (operator : Space →L[ℝ] Space) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (operatorBound : ‖operator‖ ≤ bound) (depth : ℕ) :
    ‖NormedSpace.exp operator - polynomial operator depth‖ ≤ scalarTail bound depth := by
  have powerBound : ∀ index : ℕ, ‖operator ^ index‖ ≤ bound ^ index := by
    intro index
    induction index with
    | zero => simpa only [pow_zero] using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Space))
    | succ index inductionBound =>
        rw [pow_succ]
        exact (norm_mul_le _ _).trans (by
          simpa only [pow_succ] using mul_le_mul inductionBound operatorBound (norm_nonneg _) (pow_nonneg boundNonnegative index))
  have coefficientBound (index : ℕ) :
      ‖(index.factorial : ℝ)⁻¹ • operator ^ index‖ ≤ (index.factorial : ℝ)⁻¹ * bound ^ index := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (index.factorial : ℝ)⁻¹)]
    exact mul_le_mul_of_nonneg_left (powerBound index) (by positivity)
  have operatorLimit : Tendsto (polynomial operator) atTop (nhds (NormedSpace.exp operator)) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) operator).tendsto_sum_nat
  have scalarSum : HasSum (fun index : ℕ => (index.factorial : ℝ)⁻¹ * bound ^ index) (Real.exp bound) := by
    simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) bound
  apply le_of_tendsto_of_tendsto
    ((operatorLimit.sub_const (polynomial operator depth)).norm)
    (scalarSum.tendsto_sum_nat.sub_const
      (∑ index ∈ Finset.range depth, (index.factorial : ℝ)⁻¹ * bound ^ index))
  filter_upwards [eventually_ge_atTop depth] with length lengthLarge
  unfold polynomial
  rw [Finset.sum_range_sub_sum_range lengthLarge, Finset.sum_range_sub_sum_range lengthLarge]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun index _ => coefficientBound index)

theorem yosida_generator_norm_bound
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
    (resolvent : Space →L[ℝ] Space) (contraction : ‖resolvent‖ ≤ 1)
    (step : ℝ) (stepPositive : 0 < step) :
    ‖BoundedYosida.generator resolvent step‖ ≤ 2 / step := by
  rw [BoundedYosida.generator, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr stepPositive)]
  calc
    step⁻¹ * ‖1 - resolvent‖ ≤ step⁻¹ * (1 + 1) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr stepPositive.le)
      exact (norm_sub_le _ _).trans (add_le_add (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Space)) contraction)
    _ = 2 / step := by ring

end VaryingBoundedExponential

namespace VaryingHilbertCore

variable {Core Hilbert : Type*} [AddCommGroup Core] [Module ℝ Core]
    [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert] [CompleteSpace Hilbert]
    {LevelHilbert : ℕ → Type*} [∀ level, NormedAddCommGroup (LevelHilbert level)]
    [∀ level, InnerProductSpace ℝ (LevelHilbert level)] [∀ level, CompleteSpace (LevelHilbert level)]

theorem strong_const_smul (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (scalar : ℝ) {sequence : ∀ level, LevelHilbert level} {limit : Hilbert}
    (convergence : core.Strong sequence limit) :
    core.Strong (fun level => scalar • sequence level) (scalar • limit) := by
  intro tolerance tolerancePositive
  obtain ⟨element, limitClose, sequenceClose⟩ :=
    convergence (tolerance / (|scalar| + 1)) (by positivity)
  refine ⟨scalar • element, ?_, ?_⟩
  · rw [map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]
    have small := (lt_div_iff₀ (by positivity : 0 < |scalar| + 1)).mp limitClose
    nlinarith [norm_nonneg (core.embed element - limit)]
  · filter_upwards [sequenceClose] with level close
    rw [map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]
    have small := (lt_div_iff₀ (by positivity : 0 < |scalar| + 1)).mp close
    nlinarith [norm_nonneg (sequence level - core.restrict level element)]

theorem strong_operator_powers
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (operators : ∀ level, LevelHilbert level →L[ℝ] LevelHilbert level) (operator : Hilbert →L[ℝ] Hilbert)
    (operatorStrong : ∀ (sequence : ∀ level, LevelHilbert level) (limit : Hilbert),
      core.Strong sequence limit → core.Strong (fun level => operators level (sequence level)) (operator limit))
    (sequence : ∀ level, LevelHilbert level) (limit : Hilbert) (convergence : core.Strong sequence limit)
    (power : ℕ) : core.Strong (fun level => (operators level ^ power) (sequence level)) ((operator ^ power) limit) := by
  induction power with
  | zero => simpa only [pow_zero, ContinuousLinearMap.one_apply] using convergence
  | succ power induction =>
      simpa only [pow_succ', ContinuousLinearMap.mul_apply] using operatorStrong _ _ induction

theorem strong_operator_polynomial
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (operators : ∀ level, LevelHilbert level →L[ℝ] LevelHilbert level) (operator : Hilbert →L[ℝ] Hilbert)
    (operatorStrong : ∀ (sequence : ∀ level, LevelHilbert level) (limit : Hilbert),
      core.Strong sequence limit → core.Strong (fun level => operators level (sequence level)) (operator limit))
    (sequence : ∀ level, LevelHilbert level) (limit : Hilbert) (convergence : core.Strong sequence limit)
    (depth : ℕ) :
    core.Strong (fun level => VaryingBoundedExponential.polynomial (operators level) depth (sequence level))
      (VaryingBoundedExponential.polynomial operator depth limit) := by
  induction depth with
  | zero =>
      simpa only [VaryingBoundedExponential.polynomial, Finset.range_zero, Finset.sum_empty,
        ContinuousLinearMap.zero_apply, map_zero] using core.strong_restrict (0 : Core)
  | succ depth induction =>
      simpa only [VaryingBoundedExponential.polynomial, Finset.sum_range_succ,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply] using
        core.strong_add induction
          (core.strong_const_smul (depth.factorial : ℝ)⁻¹
            (core.strong_operator_powers operators operator operatorStrong sequence limit convergence depth))

theorem strong_exp_apply_of_uniform_bound
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (operators : ∀ level, LevelHilbert level →L[ℝ] LevelHilbert level) (operator : Hilbert →L[ℝ] Hilbert)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (operatorsBound : ∀ level, ‖operators level‖ ≤ bound) (operatorBound : ‖operator‖ ≤ bound)
    (operatorStrong : ∀ (sequence : ∀ level, LevelHilbert level) (limit : Hilbert),
      core.Strong sequence limit → core.Strong (fun level => operators level (sequence level)) (operator limit))
    (sequence : ∀ level, LevelHilbert level) (limit : Hilbert) (convergence : core.Strong sequence limit) :
    core.Strong (fun level => NormedSpace.exp (operators level) (sequence level)) (NormedSpace.exp operator limit) := by
  obtain ⟨normBound, sequenceNormBound⟩ := core.weak_norm_bounded (core.strong_implies_weak convergence)
  have normBoundNonnegative : 0 ≤ normBound := (norm_nonneg (sequence 0)).trans (sequenceNormBound 0)
  let commonBound := normBound + ‖limit‖ + 1
  have commonPositive : 0 < commonBound := by dsimp [commonBound]; positivity
  have sequenceBound : ∀ level, ‖sequence level‖ ≤ commonBound := by
    intro level
    dsimp only [commonBound]
    linarith [sequenceNormBound level, norm_nonneg limit]
  have targetBound : ‖limit‖ ≤ commonBound := by dsimp only [commonBound]; linarith
  intro tolerance tolerancePositive
  obtain ⟨depth, tailSmall⟩ :=
    ((VaryingBoundedExponential.scalarTail_tendsto bound).eventually_lt_const
      (by positivity : 0 < tolerance / (3 * commonBound))).exists
  have tailNonnegative : 0 ≤ VaryingBoundedExponential.scalarTail bound depth :=
    (norm_nonneg _).trans (VaryingBoundedExponential.norm_exp_sub_polynomial_le operator bound boundNonnegative operatorBound depth)
  have tailProductSmall : VaryingBoundedExponential.scalarTail bound depth * commonBound < tolerance / 3 := by
    have small := (lt_div_iff₀ (by positivity : 0 < 3 * commonBound)).mp tailSmall
    nlinarith
  have nativeError (level : ℕ) :
      ‖NormedSpace.exp (operators level) (sequence level) -
        VaryingBoundedExponential.polynomial (operators level) depth (sequence level)‖ < tolerance / 3 := by
    rw [← ContinuousLinearMap.sub_apply]
    apply lt_of_le_of_lt _ tailProductSmall
    exact ((NormedSpace.exp (operators level) - VaryingBoundedExponential.polynomial (operators level) depth).le_opNorm
      (sequence level)).trans (mul_le_mul
        (VaryingBoundedExponential.norm_exp_sub_polynomial_le (operators level) bound boundNonnegative (operatorsBound level) depth)
        (sequenceBound level) (norm_nonneg _) tailNonnegative)
  have targetError : ‖NormedSpace.exp operator limit - VaryingBoundedExponential.polynomial operator depth limit‖ < tolerance / 3 := by
    rw [← ContinuousLinearMap.sub_apply]
    apply lt_of_le_of_lt _ tailProductSmall
    exact ((NormedSpace.exp operator - VaryingBoundedExponential.polynomial operator depth).le_opNorm limit).trans
      (mul_le_mul (VaryingBoundedExponential.norm_exp_sub_polynomial_le operator bound boundNonnegative operatorBound depth)
        targetBound (norm_nonneg _) tailNonnegative)
  obtain ⟨element, limitClose, sequenceClose⟩ :=
    core.strong_operator_polynomial operators operator operatorStrong sequence limit convergence depth
      (tolerance / 3) (by positivity)
  refine ⟨element, ?_, ?_⟩
  · have triangle : ‖core.embed element - NormedSpace.exp operator limit‖ ≤
        ‖core.embed element - VaryingBoundedExponential.polynomial operator depth limit‖ +
          ‖VaryingBoundedExponential.polynomial operator depth limit - NormedSpace.exp operator limit‖ := by
      calc
        _ = ‖(core.embed element - VaryingBoundedExponential.polynomial operator depth limit) +
          (VaryingBoundedExponential.polynomial operator depth limit - NormedSpace.exp operator limit)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [norm_sub_rev (VaryingBoundedExponential.polynomial operator depth limit)] at triangle
    linarith
  · filter_upwards [sequenceClose] with level close
    have triangle : ‖NormedSpace.exp (operators level) (sequence level) - core.restrict level element‖ ≤
        ‖NormedSpace.exp (operators level) (sequence level) -
          VaryingBoundedExponential.polynomial (operators level) depth (sequence level)‖ +
        ‖VaryingBoundedExponential.polynomial (operators level) depth (sequence level) - core.restrict level element‖ := by
      calc
        _ = ‖(NormedSpace.exp (operators level) (sequence level) -
          VaryingBoundedExponential.polynomial (operators level) depth (sequence level)) +
          (VaryingBoundedExponential.polynomial (operators level) depth (sequence level) - core.restrict level element)‖ := by rw [sub_add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith [nativeError level]

end VaryingHilbertCore
end IGS.Sec31

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators

variable {K : ℕ}

noncomputable def xiNativeYosidaSemigroup (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ) (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (step : ℝ) (stepPositive : 0 < step) (time : ℝ) :
    Lp ℝ 2 (xiVertexSpeedMeasure system mass level) →L[ℝ] Lp ℝ 2 (xiVertexSpeedMeasure system mass level) :=
  BoundedYosida.semigroup
    (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level
      resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive) step time

theorem xiNativeYosidaSemigroup_strong_limit (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector))) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass))),
      ∀ (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1) (time : ℝ)
        (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass)),
      core.Strong forcing target →
      core.Strong (fun level => xiNativeYosidaSemigroup system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive time (forcing level))
        (QuadraticEnergySpace.yosidaSemigroup originalDomain originalForm nonnegative closable
          originalDense step stepPositive stepAtMostOne time target) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  dsimp only
  intro originalDense step stepPositive stepAtMostOne time forcing target forcingStrong
  have resolventStrong : ∀ (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
      (limit : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass)),
      core.Strong sequence limit →
        core.Strong (fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (sequence level))
          (QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable originalDense
            step stepPositive stepAtMostOne limit) :=
    xiNativeFiniteResolvent_strong_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive
      normalizedConvergence originalDense step stepPositive stepAtMostOne
  have generatorStrong : ∀ (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
      (limit : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass)),
      core.Strong sequence limit →
        core.Strong (fun level => BoundedYosida.generator
          (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level
            resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive) step (sequence level))
          (BoundedYosida.generator
            (QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable originalDense
              step stepPositive stepAtMostOne) step limit) := by
    intro sequence limit convergence
    have scaled := core.strong_const_smul step⁻¹
      (core.strong_sub convergence (resolventStrong sequence limit convergence))
    simpa only [BoundedYosida.generator, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] using scaled
  have nativeBound (level : ℕ) :
      ‖(-time) • BoundedYosida.generator
        (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level
          resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive) step‖ ≤
        |time| * (2 / step) := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    exact mul_le_mul_of_nonneg_left
      (VaryingBoundedExponential.yosida_generator_norm_bound _
        (xiNativeFiniteResolvent_properties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive).2
        step stepPositive) (abs_nonneg time)
  have targetBound :
      ‖(-time) • BoundedYosida.generator
        (QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable originalDense
          step stepPositive stepAtMostOne) step‖ ≤ |time| * (2 / step) := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg]
    exact mul_le_mul_of_nonneg_left
      (VaryingBoundedExponential.yosida_generator_norm_bound _
        (QuadraticEnergySpace.smallStepResolvent_operator_norm originalDomain originalForm nonnegative closable originalDense
          step stepPositive stepAtMostOne) step stepPositive) (abs_nonneg time)
  have exponentialStrong := core.strong_exp_apply_of_uniform_bound
    (fun level => (-time) • BoundedYosida.generator
      (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level
        resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive) step)
    ((-time) • BoundedYosida.generator
      (QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable originalDense
        step stepPositive stepAtMostOne) step)
    (|time| * (2 / step)) (by positivity) nativeBound targetBound
    (fun sequence limit convergence => by
      simpa only [ContinuousLinearMap.smul_apply] using
        core.strong_const_smul (-time) (generatorStrong sequence limit convergence))
    forcing target forcingStrong
  simpa only [xiNativeYosidaSemigroup, QuadraticEnergySpace.yosidaSemigroup, BoundedYosida.semigroup] using exponentialStrong

theorem exists_xiNativeYosidaStrong_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
        (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive
      let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
        intro sequence energyCauchy ambientZero
        exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
          mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
          (by simpa using ambientZero.norm)
      ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass))),
        ∀ (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1) (time : ℝ)
          (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
          (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass)),
        core.Strong forcing target →
        core.Strong (fun level => xiNativeYosidaSemigroup system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive time (forcing level))
          (QuadraticEnergySpace.yosidaSemigroup originalDomain originalForm nonnegative closable
            originalDense step stepPositive stepAtMostOne time target) := by
  classical
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
      originalDense, originalNonnegative⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, originalDense, ?_⟩
  exact xiNativeYosidaSemigroup_strong_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense

end EIGS

#print axioms IGS.Sec31.VaryingBoundedExponential.scalarTail_tendsto
#print axioms IGS.Sec31.VaryingBoundedExponential.norm_exp_sub_polynomial_le
#print axioms IGS.Sec31.VaryingBoundedExponential.yosida_generator_norm_bound
#print axioms IGS.Sec31.VaryingHilbertCore.strong_const_smul
#print axioms IGS.Sec31.VaryingHilbertCore.strong_operator_powers
#print axioms IGS.Sec31.VaryingHilbertCore.strong_operator_polynomial
#print axioms IGS.Sec31.VaryingHilbertCore.strong_exp_apply_of_uniform_bound
#print axioms EIGS.xiNativeYosidaSemigroup_strong_limit

#print axioms EIGS.exists_xiNativeYosidaStrong_of_rules
