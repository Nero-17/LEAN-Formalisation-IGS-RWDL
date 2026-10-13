import RequestProject.Section31.EIGSL2QuadraticEnergy

/-! Constants belong to the actual native L² energy domain and have zero
quadratic energy. This supplies the constant part of conservativeness at the
constructed core, without claiming that a closed form has been obtained. -/

namespace EIGS

open MeasureTheory IGS.Sec31
open scoped ENNReal

variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)

theorem xiContinuousFiniteEnergyDomain_const (value : ℝ) :
    ContinuousMap.const _ value ∈
      xiContinuousFiniteEnergyDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive := by
  change ∃ bound : ℝ, ∀ level,
    (xiUnionWeightedNetwork system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive level).energy
      (fun _ => value) ≤ bound
  refine ⟨0, fun level => ?_⟩
  simp [FiniteNetwork.energy]

noncomputable def xiContinuousLpEnergyConstant (value : ℝ) :
    xiContinuousEnergyLpDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive :=
  xiContinuousEnergyLpEquiv system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
    resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      ⟨ContinuousMap.const _ value,
        xiContinuousFiniteEnergyDomain_const system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
          resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive value⟩

theorem xiContinuousLpEnergyConstant_ae (value : ℝ) :
    ((xiContinuousLpEnergyConstant system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive value :
        Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)) :
      XiMetricCompletion system connected lengths lengthsPositive rate (zero_lt_one.trans rateGreaterThanOne) eigenpair → ℝ)
        =ᵐ[xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass]
      fun _ => value := by
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2)
    (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
    (ContinuousMap.const _ value)

theorem xiContinuousLpEnergyConstant_energy
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (value : ℝ) :
    xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
      (xiContinuousLpEnergyConstant system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive value) = 0 := by
  rw [xiContinuousLpEnergyConstant, xiContinuousLpEnergyQuadraticForm_of_continuous]
  simp [xiExtendedWeightedEnergy, extendedTraceEnergy, FiniteNetwork.energy]

end EIGS

#print axioms EIGS.xiContinuousFiniteEnergyDomain_const
#print axioms EIGS.xiContinuousLpEnergyConstant_ae
#print axioms EIGS.xiContinuousLpEnergyConstant_energy
