import RequestProject.Section31.EIGSL2EnergyRepresentative

/-! The actual finite-energy continuous functions form a subspace of the
constructed limit L². Full support transports their concrete trace quadratic
energy to that subspace, without asserting closedness of the form. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31
open scoped ENNReal

variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)

noncomputable def xiContinuousEnergyToUnionDomain :
    xiContinuousFiniteEnergyDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive →ₗ[ℝ]
    xiWeightedEnergyDomain system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive where
  toFun function := ⟨xiContinuousUnionRestriction system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair function, function.property⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

noncomputable def xiContinuousEnergyLpEquiv :
    xiContinuousFiniteEnergyDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive ≃ₗ[ℝ]
    xiContinuousEnergyLpDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive :=
  Submodule.equivMapOfInjective
    (xiContinuousL2Map system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).toLinearMap
    (xiContinuousL2Map_injective system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
    (xiContinuousFiniteEnergyDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive)

variable (renormalizationEigenpair : ∀ colour,
    (system.ruleFamily connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)

noncomputable def xiContinuousLpEnergyQuadraticForm :
    QuadraticForm ℝ (xiContinuousEnergyLpDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive) :=
  ((limitTraceQuadraticForm
    (xiUnionWeightedNetwork system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive)
    (xiUnionWeightedNetwork_energy_increasing_of_eigenpair system connected resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive renormalizationEigenpair)).comp
    (xiContinuousEnergyToUnionDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive)).comp
    (xiContinuousEnergyLpEquiv system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive).symm.toLinearMap

theorem xiContinuousLpEnergyQuadraticForm_nonnegative
    (function : xiContinuousEnergyLpDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive) :
    0 ≤ xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair function :=
  limitTraceQuadraticForm_nonneg _
    (xiUnionWeightedNetwork_energy_increasing_of_eigenpair system connected resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive renormalizationEigenpair) _

theorem xiContinuousLpEnergyQuadraticForm_of_continuous
    (function : xiContinuousFiniteEnergyDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive) :
    xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
      (xiContinuousEnergyLpEquiv system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive function) =
    (xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      ((function : C(XiMetricCompletion system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair, ℝ)) ∘
        xiCompletionUnionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair)).toReal := by
  unfold xiContinuousLpEnergyQuadraticForm
  simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rfl

theorem xiContinuousLpEnergyQuadraticForm_finite_energy_limit
    (function : xiContinuousEnergyLpDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive) :
    Tendsto (fun level =>
      (xiUnionWeightedNetwork system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive level).energy
        (xiContinuousEnergyToUnionDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
          resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          ((xiContinuousEnergyLpEquiv system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
            resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive).symm function))) atTop
      (nhds (xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair function)) :=
  finite_energy_tendsto_traceEnergyValue _
    (xiUnionWeightedNetwork_energy_increasing_of_eigenpair system connected resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive renormalizationEigenpair) _

end EIGS

#print axioms EIGS.xiContinuousEnergyLpEquiv
#print axioms EIGS.xiContinuousLpEnergyQuadraticForm_nonnegative
#print axioms EIGS.xiContinuousLpEnergyQuadraticForm_of_continuous
#print axioms EIGS.xiContinuousLpEnergyQuadraticForm_finite_energy_limit
