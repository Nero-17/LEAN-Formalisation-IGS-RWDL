import RequestProject.Section31.EIGSCompletedResistanceTriangle
import RequestProject.Section31.EIGSContinuousResistanceFormCore

/-! All-point variational resistance for the actual continuous energy form.
Every continuous finite-energy function has a unique representative in the
complete pure-energy Hilbert space modulo constants. The same completed Riesz
rows give a sharp finite energy bound and an actual function attaining it.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31
noncomputable section
variable {K : ℕ}
variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (anchor : XiVertexUnion system)

local instance : CompactSpace (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :=
  xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair

variable (extension : XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair anchor →L[ℝ]
  C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (agreement : ∀ values vertex, extension values (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) = values.value.val vertex)

include agreement in
theorem exists_unique_xiContinuousEnergy_zero_anchored_representative
    (function : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive) :
    ∃! representative : xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive resistanceVector
        vectorPositive eigenpair anchor,
      extension representative.val = function.val - ContinuousMap.const _
        (function.val (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair anchor)) ∧
      ‖representative‖ ^ 2 = xiContinuousResistanceQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair function := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let values := xiContinuousEnergyToUnionDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive function
  obtain ⟨representative, representativeProperty, unique⟩ := exists_unique_xiEnergy_zero_anchored_representative system rulesConnected
    resistanceRate ratePositive resistanceVector vectorPositive anchor eigenpair values
  have continuousAgreement : extension representative.val = function.val - ContinuousMap.const _
      (function.val (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair anchor)) := by
    apply ContinuousMap.ext
    intro point
    refine (xiCompletionUnionEmbedding_denseRange system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair).induction_on point
      (isClosed_eq (extension representative.val).continuous (function.val - ContinuousMap.const _ _).continuous) ?_
    intro vertex
    rw [agreement, representativeProperty.1]
    rfl
  refine ⟨representative, ⟨continuousAgreement, representativeProperty.2⟩, ?_⟩
  intro other otherProperty
  apply unique other
  constructor
  · intro vertex
    have equality := congrArg (fun continuous => continuous (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex)) otherProperty.1
    dsimp only at equality
    rw [agreement] at equality
    exact equality
  · exact otherProperty.2

theorem xiCompletedResistanceRow_sub_represents
    (first second : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
    (values : xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair anchor) :
    inner ℝ
      (xiCompletedResistanceRow system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension first -
        xiCompletedResistanceRow system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension second) values =
      extension values.val first - extension values.val second := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  rw [inner_sub_left]
  unfold xiCompletedResistanceRow
  rw [← continuousOperatorKernelRow_represents, ← continuousOperatorKernelRow_represents]
  rfl

include agreement in
theorem xiCompletedResistance_sharp_continuous_energy_bound
    (first second : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
    (function : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive) :
    (function.val first - function.val second) ^ 2 ≤
      xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension first second *
      xiContinuousResistanceQuadraticForm system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair function := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  obtain ⟨representative, representativeProperty, _⟩ := exists_unique_xiContinuousEnergy_zero_anchored_representative
    system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate
    ratePositive resistanceVector vectorPositive eigenpair anchor extension agreement function
  let rowDifference := xiCompletedResistanceRow system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension first -
    xiCompletedResistanceRow system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension second
  have differenceIdentity : inner ℝ rowDifference representative = function.val first - function.val second := by
    rw [xiCompletedResistanceRow_sub_represents, representativeProperty.1]
    change function.val first - _ - (function.val second - _) = _
    simp only [ContinuousMap.const_apply]
    ring
  have bound := abs_real_inner_le_norm rowDifference representative
  have squared := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg representative))).2 bound
  rw [sq_abs, mul_pow, differenceIdentity, representativeProperty.2] at squared
  exact squared

include agreement in
theorem exists_xiCompletedResistance_attaining_function
    (first second : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :
    ∃ function : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive,
      function.val first - function.val second =
        xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension first second ∧
      xiContinuousResistanceQuadraticForm system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair function =
        xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension first second := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let representative := xiCompletedResistanceRow system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension first -
    xiCompletedResistanceRow system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension second
  have restrictionIdentity : extension representative.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair = representative.val.value.val :=
    funext (agreement representative.val)
  have finiteEnergy : extension representative.val ∈ xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive := by
    change extension representative.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair ∈
        xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive
    rw [restrictionIdentity]
    exact representative.val.value.property
  refine ⟨⟨extension representative.val, finiteEnergy⟩, ?_, ?_⟩
  · change extension representative.val first - extension representative.val second = ‖representative‖ ^ 2
    rw [← xiCompletedResistanceRow_sub_represents system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair
      anchor extension first second representative, real_inner_self_eq_norm_sq]
  · rw [xiContinuousResistanceQuadraticForm_value, restrictionIdentity, ← xiZeroAnchoredEnergyDomain_norm_sq]
    rfl

end
end EIGS

#print axioms EIGS.exists_unique_xiContinuousEnergy_zero_anchored_representative
#print axioms EIGS.xiCompletedResistance_sharp_continuous_energy_bound
#print axioms EIGS.exists_xiCompletedResistance_attaining_function
