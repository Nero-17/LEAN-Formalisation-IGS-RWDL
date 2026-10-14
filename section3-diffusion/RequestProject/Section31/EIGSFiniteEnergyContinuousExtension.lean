import RequestProject.Section31.EIGSHarmonicUnionSupComparison
import RequestProject.Section31.EIGSWeightedStepSupEnergy
import RequestProject.Section31.GeometricContinuousExtension
import RequestProject.Section31.EIGSLimitEnergy
import RequestProject.Section31.EIGSMovingStartApproximation

/-! Every actual bounded-trace-energy skeleton function has a continuous
extension to the original path-metric completion when the resistance rate
exceeds one. Continuity is constructed by uniform convergence of harmonic
interpolants, and exact skeleton agreement preserves the extended energy.
Candidate source: compilation is not claimed. -/

namespace IGS.Sec31

theorem abs_le_geometric_of_square_le
    (rate coefficient value : ℝ) (rateGreaterThanOne : 1 < rate)
    (coefficientNonnegative : 0 ≤ coefficient) (level : ℕ)
    (squareBound : value ^ 2 ≤ coefficient / rate ^ (level + 1)) :
    |value| ≤ Real.sqrt (coefficient / rate) * Real.sqrt rate⁻¹ ^ level := by
  have ratePositive := zero_lt_one.trans rateGreaterThanOne
  have inverseNonnegative := (inv_pos.mpr ratePositive).le
  have constantNonnegative := div_nonneg coefficientNonnegative ratePositive.le
  have powerSquare : (Real.sqrt rate⁻¹ ^ level) ^ 2 = rate⁻¹ ^ level := by
    rw [← pow_mul, Nat.mul_comm level 2, pow_mul, Real.sq_sqrt inverseNonnegative]
  have squareIdentity : (Real.sqrt (coefficient / rate) * Real.sqrt rate⁻¹ ^ level) ^ 2 =
      coefficient / rate ^ (level + 1) := by
    rw [mul_pow, Real.sq_sqrt constantNonnegative, powerSquare, pow_succ, inv_pow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  apply (sq_le_sq₀ (abs_nonneg value) (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _))).mp
  simpa only [sq_abs, squareIdentity] using squareBound

end IGS.Sec31

namespace EIGS
open IGS.Sec31 Filter Topology
open scoped BoundedContinuousFunction ENNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiFiniteEnergy_continuous_extension_of_step_contraction
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (rateGreaterThanOne : 1 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (contractionFactor : ℝ) (factorPositive : 0 < contractionFactor) (factorStrict : contractionFactor < 1)
    (stepContraction : ∀ level (oldValues : XiVtx system level → ℝ) (edge : XiEdge system.toRuleData (level + 1)),
      |xiHarmonicStep system rulesConnected resistanceRate (zero_lt_one.trans rateGreaterThanOne)
          resistanceVector vectorPositive eigenpair level oldValues (XiTail system (level + 1) edge) -
        xiHarmonicStep system rulesConnected resistanceRate (zero_lt_one.trans rateGreaterThanOne)
          resistanceVector vectorPositive eigenpair level oldValues (XiHead system (level + 1) edge)| ≤
        |oldValues (XiTail system level edge.1) - oldValues (XiHead system level edge.1)| * contractionFactor)
    (values : XiVertexUnion system → ℝ)
    (finiteEnergy : values ∈ xiWeightedEnergyDomain system resistanceRate (zero_lt_one.trans rateGreaterThanOne)
      resistanceVector vectorPositive) :
    ∃ extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
      (∀ vertex, extension (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) = values vertex) ∧
      xiExtendedWeightedEnergy system resistanceRate (zero_lt_one.trans rateGreaterThanOne)
        resistanceVector vectorPositive (extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths
          lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) =
        xiExtendedWeightedEnergy system resistanceRate (zero_lt_one.trans rateGreaterThanOne)
          resistanceVector vectorPositive values := by
  let ratePositive := zero_lt_one.trans rateGreaterThanOne
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  change TraceEnergyFinite (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
    values at finiteEnergy
  obtain ⟨energyBound, energyBoundValid⟩ := finiteEnergy
  have energyBoundNonnegative : 0 ≤ energyBound :=
    ((xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive 0).energy_nonneg values).trans
      (energyBoundValid 0)
  obtain ⟨stepConstant, stepConstantPositive, deviation⟩ :=
    exists_xiHarmonicStep_deviation_sup_energy_bound system rulesConnected
  let upper := ∑ colour, resistanceVector colour
  have vectorBound : ∀ colour, resistanceVector colour ≤ upper := fun colour =>
    Finset.single_le_sum (fun other _ => (vectorPositive other).le) (Finset.mem_univ colour)
  have upperPositive : 0 < upper := (vectorPositive system.initCol).trans_le (vectorBound system.initCol)
  have extensionsExist := fun level => exists_xiContinuousHarmonic_of_step_contraction system rulesConnected
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair contractionFactor factorPositive factorStrict stepContraction
      level (values ∘ xiVertexEmbedding system level)
  choose approximation approximationAgreement using extensionsExist
  let boundedApproximation := fun level => BoundedContinuousFunction.mkOfCompact (approximation level)
  let coefficient := stepConstant * upper * energyBound
  have coefficientNonnegative : 0 ≤ coefficient :=
    mul_nonneg (mul_pos stepConstantPositive upperPositive).le energyBoundNonnegative
  let constant := Real.sqrt (coefficient / resistanceRate)
  let factor := Real.sqrt resistanceRate⁻¹
  have factorNonnegative : 0 ≤ factor := Real.sqrt_nonneg _
  have factorStrict' : factor < 1 := by
    have inverseStrict := (inv_lt_one₀ ratePositive).mpr rateGreaterThanOne
    have square := Real.sq_sqrt (inv_pos.mpr ratePositive).le
    dsimp only [factor]
    nlinarith [Real.sqrt_nonneg resistanceRate⁻¹]
  have boundaryBound : ∀ level (vertex : XiVtx system (level + 1)),
      |values (xiVertexEmbedding system (level + 1) vertex) -
        xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          level (values ∘ xiVertexEmbedding system level) vertex| ≤ constant * factor ^ level := by
    intro level vertex
    have stepBound := deviation resistanceRate ratePositive resistanceVector vectorPositive eigenpair
      upper vectorBound level (values ∘ xiVertexEmbedding system (level + 1)) vertex
    have oldValues : (fun old => (values ∘ xiVertexEmbedding system (level + 1)) (Sum.inl old)) =
        values ∘ xiVertexEmbedding system level := rfl
    rw [oldValues] at stepBound
    have finiteBound : (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive
        (level + 1)).energy (values ∘ xiVertexEmbedding system (level + 1)) ≤ energyBound := energyBoundValid (level + 1)
    have enlarged := stepBound.trans (mul_le_mul_of_nonneg_left finiteBound
      (div_nonneg (mul_pos stepConstantPositive upperPositive).le (pow_pos ratePositive _).le))
    have squareBound : (values (xiVertexEmbedding system (level + 1) vertex) -
        xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          level (values ∘ xiVertexEmbedding system level) vertex) ^ 2 ≤ coefficient / resistanceRate ^ (level + 1) := by
      convert enlarged using 1 <;> dsimp only [coefficient, Function.comp_apply] <;> ring
    exact abs_le_geometric_of_square_le resistanceRate coefficient _ rateGreaterThanOne coefficientNonnegative
      level squareBound
  have increments : ∀ level, ‖boundedApproximation (level + 1) - boundedApproximation level‖ ≤ constant * factor ^ level := by
    intro level
    have unionBound := xiHarmonicUnionExtension_successor_sub_bound system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair level values (constant * factor ^ level) (boundaryBound level)
    have pointBound : ∀ point, |approximation (level + 1) point - approximation level point| ≤ constant * factor ^ level := by
      intro point
      refine (xiCompletionUnionEmbedding_denseRange system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair).induction_on point
        (isClosed_le (((approximation (level + 1)).continuous.sub (approximation level).continuous).abs) continuous_const) ?_
      intro vertex
      rw [approximationAgreement, approximationAgreement]
      exact unionBound vertex
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg factorNonnegative _))).mpr
    intro point
    change ‖approximation (level + 1) point - approximation level point‖ ≤ constant * factor ^ level
    simpa only [Real.norm_eq_abs] using pointBound point
  have agreement : ∀ vertex, ∀ᶠ level in atTop,
      boundedApproximation level (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) = values vertex := by
    intro vertex
    obtain ⟨birth, membership⟩ := xiVertexUnion_exhausted system vertex
    filter_upwards [eventually_ge_atTop birth] with level afterBirth
    obtain ⟨finiteVertex, rfl⟩ := xiLevelVertices_monotone system afterBirth membership
    change approximation level _ = _
    rw [approximationAgreement]
    exact xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair level (values ∘ xiVertexEmbedding system level) 0 finiteVertex
  obtain ⟨extension, convergence, extensionAgreement⟩ := exists_continuous_extension_of_geometric_uniform_increments
    (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) values boundedApproximation constant factor
      factorNonnegative factorStrict' increments agreement
  refine ⟨extension.toContinuousMap, extensionAgreement, ?_⟩
  exact congrArg (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive)
    (funext extensionAgreement)

end
end EIGS

#print axioms IGS.Sec31.abs_le_geometric_of_square_le
#print axioms EIGS.exists_xiFiniteEnergy_continuous_extension_of_step_contraction
