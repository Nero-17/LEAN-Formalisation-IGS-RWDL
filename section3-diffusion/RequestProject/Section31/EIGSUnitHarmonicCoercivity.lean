import RequestProject.Section31.EIGSUnitL2Gram
import RequestProject.Section31.EIGSHarmonicBoundaryL2
import RequestProject.Section31.EIGSUnitPerronRecovery
import RequestProject.Section31.EIGSUnitProjectionAlgebra

/-! Eventual uniform control of fixed finite boundary coordinates by the actual
original-unit harmonic native L² norms. The finite Gram convergence used below
is proved for the actual unit minimizers and their actual continuous limits. -/

open Filter Topology
open scoped BigOperators BoundedContinuousFunction

private theorem finite_linear_norm_square {Index Space : Type*}
    [Fintype Index] [DecidableEq Index] [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    (linear : (Index → ℝ) →ₗ[ℝ] Space) (values : Index → ℝ) :
    ‖linear values‖ ^ 2 = ∑ first, ∑ second,
      values first * values second * inner ℝ (linear (Pi.single first 1)) (linear (Pi.single second 1)) := by
  have reconstruction : (∑ index, values index • (Pi.single index (1 : ℝ) : Index → ℝ)) = values := by
    ext index
    simp [Finset.sum_apply, Pi.single_apply, eq_comm]
  have representation : linear values = ∑ index, values index • linear (Pi.single index 1) := by
    calc
      linear values = linear (∑ index, values index • (Pi.single index (1 : ℝ) : Index → ℝ)) := congrArg linear reconstruction.symm
      _ = _ := by simp
  rw [← real_inner_self_eq_norm_sq, representation]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, mul_assoc]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [real_inner_comm (linear (Pi.single second 1)) (linear (Pi.single first 1))]

private theorem finite_gram_eventual_coercivity {Index LimitSpace : Type*}
    [Fintype Index] [DecidableEq Index] [NormedAddCommGroup LimitSpace] [InnerProductSpace ℝ LimitSpace]
    (NativeSpace : ℕ → Type*) [∀ level, NormedAddCommGroup (NativeSpace level)]
    [∀ level, InnerProductSpace ℝ (NativeSpace level)]
    (native : ∀ level, (Index → ℝ) →ₗ[ℝ] NativeSpace level)
    (limit : (Index → ℝ) →ₗ[ℝ] LimitSpace)
    (bound : ℝ) (boundPositive : 0 < bound)
    (limitBound : ∀ values, ‖values‖ ≤ bound * ‖limit values‖)
    (gramConvergence : ∀ first second,
      Tendsto (fun level => inner ℝ (native level (Pi.single first 1)) (native level (Pi.single second 1)))
        atTop (nhds (inner ℝ (limit (Pi.single first 1)) (limit (Pi.single second 1))))) :
    ∀ᶠ level in atTop, ∀ values, ‖values‖ ≤ (2 * bound) * ‖native level values‖ := by
  have errorsTendsto : Tendsto (fun level => ∑ first, ∑ second,
      |inner ℝ (limit (Pi.single first 1)) (limit (Pi.single second 1)) -
        inner ℝ (native level (Pi.single first 1)) (native level (Pi.single second 1))|) atTop (nhds 0) := by
    have entryTendsto : ∀ first second, Tendsto (fun level =>
        |inner ℝ (limit (Pi.single first 1)) (limit (Pi.single second 1)) -
          inner ℝ (native level (Pi.single first 1)) (native level (Pi.single second 1))|) atTop (nhds 0) := by
      intro first second
      simpa using ((gramConvergence first second).const_sub
        (inner ℝ (limit (Pi.single first 1)) (limit (Pi.single second 1)))).abs
    simpa using tendsto_finset_sum Finset.univ (fun first _ =>
      tendsto_finset_sum Finset.univ (fun second _ => entryTendsto first second))
  filter_upwards [errorsTendsto.eventually (gt_mem_nhds (by positivity : 0 < 1 / (2 * bound ^ 2)))] with level errorsSmall
  intro values
  have normDifference : ‖limit values‖ ^ 2 - ‖native level values‖ ^ 2 ≤
      (∑ first, ∑ second,
        |inner ℝ (limit (Pi.single first 1)) (limit (Pi.single second 1)) -
          inner ℝ (native level (Pi.single first 1)) (native level (Pi.single second 1))|) * ‖values‖ ^ 2 := by
    rw [finite_linear_norm_square limit values, finite_linear_norm_square (native level) values,
      ← Finset.sum_sub_distrib, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro first _
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro second _
    have coefficientBound : |values first * values second| ≤ ‖values‖ ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm values first)
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm values second) (abs_nonneg _) (norm_nonneg _)
    calc
      _ = (values first * values second) *
          (inner ℝ (limit (Pi.single first 1)) (limit (Pi.single second 1)) -
            inner ℝ (native level (Pi.single first 1)) (native level (Pi.single second 1))) := by ring
      _ ≤ |values first * values second| *
          |inner ℝ (limit (Pi.single first 1)) (limit (Pi.single second 1)) -
            inner ℝ (native level (Pi.single first 1)) (native level (Pi.single second 1))| := by
        rw [← abs_mul]
        exact le_abs_self _
      _ ≤ _ := by
        exact (mul_le_mul_of_nonneg_right coefficientBound (abs_nonneg
          (inner ℝ (limit (Pi.single first 1)) (limit (Pi.single second 1)) -
            inner ℝ (native level (Pi.single first 1)) (native level (Pi.single second 1))))).trans_eq (mul_comm _ _)
  have lowerBound := pow_le_pow_left₀ (norm_nonneg values) (limitBound values) 2
  have errorBound := mul_le_mul_of_nonneg_right errorsSmall.le (sq_nonneg ‖values‖)
  have normComparison : ‖values‖ ^ 2 ≤ 2 * bound ^ 2 * ‖native level values‖ ^ 2 := by
    rw [mul_pow] at lowerBound
    have divisionIdentity : bound ^ 2 * (1 / (2 * bound ^ 2) * ‖values‖ ^ 2) = ‖values‖ ^ 2 / 2 := by
      field_simp [ne_of_gt boundPositive]
      <;> ring
    have upperBound : ‖limit values‖ ^ 2 ≤ ‖native level values‖ ^ 2 +
        1 / (2 * bound ^ 2) * ‖values‖ ^ 2 := by linarith [normDifference, errorBound]
    have scaled := mul_le_mul_of_nonneg_left upperBound (sq_nonneg bound)
    rw [mul_add, divisionIdentity] at scaled
    linarith
  have rightNonnegative : 0 ≤ (2 * bound) * ‖native level values‖ := by positivity
  nlinarith [mul_nonneg (sq_nonneg bound) (sq_nonneg ‖native level values‖)]

namespace EIGS

open MeasureTheory

variable {K : ℕ}

theorem xiUnitPotentialAt_linear (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarseLevel fineLevel : ℕ) (levelsOrdered : coarseLevel ≤ fineLevel)
    (first second : XiVtx system coarseLevel → ℝ) (firstScalar secondScalar : ℝ) :
    xiUnitPotentialAt system rulesConnected coarseLevel fineLevel levelsOrdered
      (fun vertex => firstScalar * first vertex + secondScalar * second vertex) =
    (fun vertex => firstScalar * xiUnitPotentialAt system rulesConnected coarseLevel fineLevel levelsOrdered first vertex +
      secondScalar * xiUnitPotentialAt system rulesConnected coarseLevel fineLevel levelsOrdered second vertex) := by
  have firstFixed := xiUnitEnergyProjection_eq_potentialAt system rulesConnected coarseLevel fineLevel levelsOrdered
    (xiUnitPotentialAt system rulesConnected coarseLevel fineLevel levelsOrdered first)
  have secondFixed := xiUnitEnergyProjection_eq_potentialAt system rulesConnected coarseLevel fineLevel levelsOrdered
    (xiUnitPotentialAt system rulesConnected coarseLevel fineLevel levelsOrdered second)
  simp only [xiUnitPotentialAt_boundary] at firstFixed secondFixed
  have combined := xiUnitEnergyProjection_eq_potentialAt system rulesConnected coarseLevel fineLevel levelsOrdered
    (fun vertex => firstScalar * xiUnitPotentialAt system rulesConnected coarseLevel fineLevel levelsOrdered first vertex +
      secondScalar * xiUnitPotentialAt system rulesConnected coarseLevel fineLevel levelsOrdered second vertex)
  simp only [xiUnitPotentialAt_boundary] at combined
  rw [← combined, xiUnitEnergyProjection_linear, firstFixed, secondFixed]

noncomputable def xiUnitNativeLinearMap (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (coarseLevel fineLevel : ℕ) :
    (XiVtx system coarseLevel → ℝ) →ₗ[ℝ] Lp ℝ 2 (xiVertexSpeedMeasure system mass fineLevel) where
  toFun := fun values => xiUnitNativeL2 system rulesConnected mass coarseLevel values fineLevel
  map_add' := by
    intro first second
    by_cases levelsOrdered : coarseLevel ≤ fineLevel
    · simp only [xiUnitNativeL2, dif_pos levelsOrdered]
      have linearity := xiUnitPotentialAt_linear system rulesConnected coarseLevel fineLevel levelsOrdered first second 1 1
      simp only [one_mul] at linearity
      change xiFiniteSpeedL2 system mass fineLevel (xiUnitPotentialAt system rulesConnected coarseLevel fineLevel levelsOrdered
        (fun vertex => first vertex + second vertex)) = _
      rw [linearity]
      exact MemLp.toLp_add MemLp.of_discrete MemLp.of_discrete
    · simp only [xiUnitNativeL2, dif_neg levelsOrdered, add_zero]
  map_smul' := by
    intro scalar values
    by_cases levelsOrdered : coarseLevel ≤ fineLevel
    · simp only [xiUnitNativeL2, dif_pos levelsOrdered]
      have linearity := xiUnitPotentialAt_linear system rulesConnected coarseLevel fineLevel levelsOrdered values values scalar 0
      simp only [zero_mul, add_zero] at linearity
      change xiFiniteSpeedL2 system mass fineLevel (xiUnitPotentialAt system rulesConnected coarseLevel fineLevel levelsOrdered
        (fun vertex => scalar * values vertex)) = _
      rw [linearity]
      exact MemLp.toLp_const_smul scalar MemLp.of_discrete
    · simp only [xiUnitNativeL2, dif_neg levelsOrdered, smul_zero]

theorem exists_xiUnitHarmonic_eventual_coercivity (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (coarseLevel : ℕ) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ᶠ fineLevel in atTop,
      ∀ values : XiVtx system coarseLevel → ℝ,
        ‖values‖ ≤ constant * ‖xiUnitNativeL2 system rulesConnected mass coarseLevel values fineLevel‖ := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  obtain ⟨extensionMap, extensionAgreement, extensionInjective, bound, boundPositive, inverseBound⟩ :=
    exists_xiHarmonic_boundary_L2_control system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass distancePositive oneColourDistance resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair coarseLevel
  obtain ⟨normalization, normalizationPositive, uniformRecovery⟩ :=
    exists_xiUnitPotential_uniform_energy_convergence_for_eigenpair system rulesConnected distancePositive
      oneColourDistance resistanceRate ratePositive resistanceVector vectorPositive eigenpair
  have extensionUniform : ∀ values : XiVtx system coarseLevel → ℝ,
      Tendsto (xiUnitPotentialUniformError system rulesConnected coarseLevel values
        (extensionMap values ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)) atTop (nhds 0) := by
    intro values
    have agreement : extensionMap values ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair =
        xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          eigenpair coarseLevel values := funext (extensionAgreement values)
    rw [agreement]
    exact (uniformRecovery coarseLevel values).1
  let native := xiUnitNativeLinearMap system rulesConnected mass coarseLevel
  let limit := (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass).toLinearMap.comp extensionMap
  have gramConvergence : ∀ first second : XiVtx system coarseLevel,
      Tendsto (fun fineLevel => inner ℝ (native fineLevel (Pi.single first 1)) (native fineLevel (Pi.single second 1)))
        atTop (nhds (inner ℝ (limit (Pi.single first 1)) (limit (Pi.single second 1)))) := by
    intro first second
    exact xiUnitNativeL2_inner_tendsto_of_uniform system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass coarseLevel coarseLevel (Pi.single first 1) (Pi.single second 1)
      (extensionMap (Pi.single first 1)) (extensionMap (Pi.single second 1))
      (extensionUniform (Pi.single first 1)) (extensionUniform (Pi.single second 1))
  refine ⟨2 * bound, by positivity, ?_⟩
  exact finite_gram_eventual_coercivity
    (fun fineLevel => Lp ℝ 2 (xiVertexSpeedMeasure system mass fineLevel)) native limit bound boundPositive inverseBound gramConvergence

end EIGS

#print axioms EIGS.xiUnitPotentialAt_linear
#print axioms EIGS.xiUnitNativeLinearMap
#print axioms EIGS.exists_xiUnitHarmonic_eventual_coercivity
