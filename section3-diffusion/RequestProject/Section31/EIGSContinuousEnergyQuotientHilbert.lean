import RequestProject.Section31.EIGSCompletedResistanceVariational

/-! The quotient of the actual continuous energy domain by constants is
linearly identified with the previously constructed complete pure-energy
Hilbert space. Surjectivity uses the actual continuous extension; the norm
squared is exactly the original trace energy. Candidate, not yet compiled. -/

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

def xiContinuousEnergyHilbertNormalization :
    xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive →ₗ[ℝ]
    xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor where
  toFun function := ⟨⟨⟨fun vertex => function.val (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) -
      function.val (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair anchor),
    traceEnergyDomain_sub_constant _
      (xiContinuousEnergyToUnionDomain system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive function)
      (function.val (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair anchor))⟩⟩, sub_self _⟩
  map_add' := by
    intro first second
    apply Subtype.ext
    apply (AnchoredTraceEnergySpace.equivDomain _ _ _ _).injective
    apply Subtype.ext
    funext vertex
    change (_ + _) - (_ + _) = (_ - _) + (_ - _)
    ring
  map_smul' := by
    intro scalar function
    apply Subtype.ext
    apply (AnchoredTraceEnergySpace.equivDomain _ _ _ _).injective
    apply Subtype.ext
    funext vertex
    change scalar * _ - scalar * _ = scalar * (_ - _)
    ring

theorem xiContinuousEnergyHilbertNormalization_energy
    (function : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive) :
    ‖xiContinuousEnergyHilbertNormalization system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor function‖ ^ 2 =
    xiContinuousResistanceQuadraticForm system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair function := by
  rw [xiZeroAnchoredEnergyDomain_norm_sq, xiContinuousResistanceQuadraticForm_value]
  exact congrArg ENNReal.toReal (extendedTraceEnergy_sub_constant _ _ _)

theorem xiContinuousEnergyHilbertNormalization_kernel
    (function : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive) :
    xiContinuousEnergyHilbertNormalization system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor function = 0 ↔
      ∃ constant : ℝ, ∀ point, function.val point = constant := by
  have normIdentity := xiContinuousEnergyHilbertNormalization_energy system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor function
  have energyKernel := xiContinuousResistanceQuadraticForm_zero_iff_constant system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair function anchor
  constructor
  · intro vanishes
    rw [vanishes, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at normIdentity
    exact ⟨_, energyKernel.mp normIdentity.symm⟩
  · rintro ⟨constant, constantValues⟩
    have zeroEnergy := energyKernel.mpr (fun point => (constantValues point).trans (constantValues _).symm)
    rw [zeroEnergy] at normIdentity
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp normIdentity)

theorem xiContinuousEnergyHilbertNormalization_surjective
    (extension : XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        eigenpair anchor →L[ℝ] C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (agreement : ∀ values vertex, extension values (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) = values.value.val vertex) :
    Function.Surjective (xiContinuousEnergyHilbertNormalization system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor) := by
  intro values
  have restrictionIdentity : extension values.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair = values.val.value.val :=
    funext (agreement values.val)
  have finiteEnergy : extension values.val ∈ xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive := by
    change extension values.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair ∈
        xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive
    rw [restrictionIdentity]
    exact values.val.value.property
  refine ⟨⟨extension values.val, finiteEnergy⟩, ?_⟩
  apply Subtype.ext
  apply (AnchoredTraceEnergySpace.equivDomain _ _ _ _).injective
  apply Subtype.ext
  funext vertex
  change extension values.val (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) -
    extension values.val (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair anchor) = values.val.value.val vertex
  rw [agreement, agreement]
  have zeroAtAnchor : values.val.value.val anchor = 0 := values.property
  rw [zeroAtAnchor, sub_zero]

end
end EIGS

#print axioms EIGS.xiContinuousEnergyHilbertNormalization_energy
#print axioms EIGS.xiContinuousEnergyHilbertNormalization_kernel
#print axioms EIGS.xiContinuousEnergyHilbertNormalization_surjective
