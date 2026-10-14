import RequestProject.Section31.EIGSFiniteEnergyContinuousExtension
import RequestProject.Section31.EIGSL2EnergyRepresentative
import RequestProject.Section31.TraceEnergyPythagoras
import Mathlib.Analysis.SpecificLimits.Basic

/-! Quantitative uniform approximation of the actual continuous energy domain
by its actual finite-level harmonic interpolants when resistanceRate > 1.
The constant is independent of the target function and level; the error is
bounded by sqrt(energy) times a geometric factor. This supplies the uniform
energy-ball approximation needed for resistance-topology identification.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31 Filter Topology
open scoped BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiContinuousHarmonicProjection_geometric_energy_tail
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
        |oldValues (XiTail system level edge.1) - oldValues (XiHead system level edge.1)| * contractionFactor) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    ∃ constant : ℝ, 0 < constant ∧
    ∀ target : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair resistanceRate (zero_lt_one.trans rateGreaterThanOne)
        resistanceVector vectorPositive,
    ∀ approximation : ℕ → C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
      (∀ level vertex, approximation level (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
          distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
        xiHarmonicUnionExtension system rulesConnected resistanceRate (zero_lt_one.trans rateGreaterThanOne)
          resistanceVector vectorPositive eigenpair level
          (target.val ∘ xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level) vertex) →
      ∀ level, ‖approximation level - target.val‖ ≤
        constant * Real.sqrt
          ((xiExtendedWeightedEnergy system resistanceRate (zero_lt_one.trans rateGreaterThanOne)
            resistanceVector vectorPositive
            (target.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal) *
        Real.sqrt resistanceRate⁻¹ ^ level := by
  let ratePositive := zero_lt_one.trans rateGreaterThanOne
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  obtain ⟨stepConstant, stepConstantPositive, deviation⟩ :=
    exists_xiHarmonicStep_deviation_sup_energy_bound system rulesConnected
  let upper := ∑ colour, resistanceVector colour
  have vectorBound : ∀ colour, resistanceVector colour ≤ upper := fun colour =>
    Finset.single_le_sum (fun other _ => (vectorPositive other).le) (Finset.mem_univ colour)
  have upperPositive : 0 < upper := (vectorPositive system.initCol).trans_le (vectorBound system.initCol)
  let factor := Real.sqrt resistanceRate⁻¹
  have factorNonnegative : 0 ≤ factor := Real.sqrt_nonneg _
  have factorStrict' : factor < 1 := by
    have inverseStrict := (inv_lt_one₀ ratePositive).mpr rateGreaterThanOne
    have square := Real.sq_sqrt (inv_pos.mpr ratePositive).le
    dsimp only [factor]
    nlinarith [Real.sqrt_nonneg resistanceRate⁻¹]
  let incrementConstant := Real.sqrt (stepConstant * upper / resistanceRate)
  have incrementPositive : 0 < incrementConstant := Real.sqrt_pos.2 (by positivity)
  refine ⟨incrementConstant / (1 - factor), div_pos incrementPositive (sub_pos.mpr factorStrict'), ?_⟩
  intro target approximation agreement
  let values := target.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair
  let energy := (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive values).toReal
  let coefficient := stepConstant * upper * energy
  have energyNonnegative : 0 ≤ energy := ENNReal.toReal_nonneg
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have squareRootIdentity : Real.sqrt (coefficient / resistanceRate) = incrementConstant * Real.sqrt energy := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ stepConstant * upper / resistanceRate)]
    congr 1
    dsimp only [coefficient]
    ring
  have boundaryBound : ∀ level (vertex : XiVtx system (level + 1)),
      |values (xiVertexEmbedding system (level + 1) vertex) -
        xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          level (values ∘ xiVertexEmbedding system level) vertex| ≤
        (incrementConstant * Real.sqrt energy) * factor ^ level := by
    intro level vertex
    have stepBound := deviation resistanceRate ratePositive resistanceVector vectorPositive eigenpair
      upper vectorBound level (values ∘ xiVertexEmbedding system (level + 1)) vertex
    have oldValues : (fun old => (values ∘ xiVertexEmbedding system (level + 1)) (Sum.inl old)) =
        values ∘ xiVertexEmbedding system level := rfl
    rw [oldValues] at stepBound
    have finiteBound := finite_energy_le_traceEnergyValue
      (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
      (⟨values, target.property⟩ : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive)
      (level + 1)
    change (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive
      (level + 1)).energy (values ∘ xiVertexEmbedding system (level + 1)) ≤ energy at finiteBound
    have enlarged := stepBound.trans (mul_le_mul_of_nonneg_left finiteBound
      (div_nonneg (mul_pos stepConstantPositive upperPositive).le (pow_pos ratePositive _).le))
    have squareBound : (values (xiVertexEmbedding system (level + 1) vertex) -
        xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          level (values ∘ xiVertexEmbedding system level) vertex) ^ 2 ≤ coefficient / resistanceRate ^ (level + 1) := by
      convert enlarged using 1 <;> dsimp only [coefficient, Function.comp_apply] <;> ring
    have absoluteBound := abs_le_geometric_of_square_le resistanceRate coefficient _ rateGreaterThanOne
      coefficientNonnegative level squareBound
    rw [squareRootIdentity] at absoluteBound
    exact absoluteBound
  have agreementUnion : ∀ level vertex, approximation level (xiCompletionUnionEmbedding system rulesConnected
      lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
      xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        eigenpair level (values ∘ xiVertexEmbedding system level) vertex := by
    intro level vertex
    exact agreement level vertex
  have increments : ∀ level, dist (approximation level) (approximation (level + 1)) ≤
      (incrementConstant * Real.sqrt energy) * factor ^ level := by
    intro level
    have unionBound := xiHarmonicUnionExtension_successor_sub_bound system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair level values
      ((incrementConstant * Real.sqrt energy) * factor ^ level) (boundaryBound level)
    rw [dist_eq_norm, norm_sub_rev]
    apply (ContinuousMap.norm_le (by positivity)).2
    intro point
    apply (xiCompletionUnionEmbedding_denseRange system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair).induction_on point
      (isClosed_le (((approximation (level + 1)).continuous.sub (approximation level).continuous).norm) continuous_const)
    intro vertex
    change ‖approximation (level + 1) _ - approximation level _‖ ≤ _
    rw [agreementUnion, agreementUnion]
    simpa only [Real.norm_eq_abs] using unionBound vertex
  have convergenceNorm := xiContinuousHarmonicProjection_uniform_tendsto system rulesConnected lengths lengthsPositive
    distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive
    eigenpair contractionFactor factorPositive factorStrict stepContraction target.val
    target.val.continuous.uniformContinuous_of_compact approximation agreement
  have convergence : Tendsto approximation atTop (𝓝 target.val) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    exact convergenceNorm
  intro level
  have tail := dist_le_of_le_geometric_of_tendsto factor (incrementConstant * Real.sqrt energy)
    factorStrict' increments convergence level
  rw [dist_eq_norm] at tail
  convert tail using 1 <;> dsimp only [factor] <;> ring

end
end EIGS

#print axioms EIGS.exists_xiContinuousHarmonicProjection_geometric_energy_tail
