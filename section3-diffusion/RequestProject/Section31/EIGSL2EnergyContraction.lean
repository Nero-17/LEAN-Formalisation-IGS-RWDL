import RequestProject.Section31.EIGSL2QuadraticEnergy

/-! Normal contractions preserve the actual L² finite-energy subspace and
decrease its constructed quadratic energy. This is a core Markov property,
separate from the still required closedness theorem. -/

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
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)

theorem xiContinuousLpEnergy_normal_contraction
    (contraction : ℝ → ℝ)
    (contractionBound : ∀ first second, |contraction first - contraction second| ≤ |first - second|)
    (function : xiContinuousEnergyLpDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive) :
    ∃ contracted : xiContinuousEnergyLpDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive,
      ((contracted : Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)) :
        XiMetricCompletion system connected lengths lengthsPositive rate (zero_lt_one.trans rateGreaterThanOne) eigenpair → ℝ) =ᵐ[
          xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass]
        contraction ∘ ((function : Lp ℝ 2
          (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)) :
          XiMetricCompletion system connected lengths lengthsPositive rate (zero_lt_one.trans rateGreaterThanOne) eigenpair → ℝ) ∧
      xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair contracted ≤
      xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair function := by
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  let representative := (xiContinuousEnergyLpEquiv system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
    resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive).symm function
  have contractionContinuous : Continuous contraction :=
    (LipschitzWith.mk_one (fun first second => by simpa only [Real.dist_eq] using contractionBound first second)).continuous
  let contractedContinuous : C(XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair, ℝ) :=
    ⟨contraction ∘ representative.val, contractionContinuous.comp representative.val.continuous⟩
  have contractedFinite : contractedContinuous ∈
      xiContinuousFiniteEnergyDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive := by
    exact traceEnergyDomain_comp _ contraction contractionBound representative.property
  let contractedRepresentative :
      xiContinuousFiniteEnergyDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive :=
    ⟨contractedContinuous, contractedFinite⟩
  let contracted := xiContinuousEnergyLpEquiv system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
    resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive contractedRepresentative
  refine ⟨contracted, ?_, ?_⟩
  · have originalEmbedding :
        xiContinuousL2Map system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass representative.val =
        (function : Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)) := by
      exact congrArg Subtype.val ((xiContinuousEnergyLpEquiv system connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair mass resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive).apply_symm_apply function)
    have originalAE := ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2)
      (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass) representative.val
    change (xiContinuousL2Map system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass representative.val :
      XiMetricCompletion system connected lengths lengthsPositive rate (zero_lt_one.trans rateGreaterThanOne) eigenpair → ℝ) =ᵐ[_]
      representative.val at originalAE
    rw [originalEmbedding] at originalAE
    have contractedAE := ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2)
      (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass) contractedContinuous
    exact contractedAE.trans (originalAE.fun_comp contraction).symm
  · have originalEnergy := xiContinuousLpEnergyQuadraticForm_of_continuous system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      renormalizationEigenpair representative
    rw [LinearEquiv.apply_symm_apply] at originalEnergy
    have contractedEnergy := xiContinuousLpEnergyQuadraticForm_of_continuous system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      renormalizationEigenpair contractedRepresentative
    rw [contractedEnergy, originalEnergy]
    apply ENNReal.toReal_mono
      ((xiWeightedEnergyDomain_iff system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive _).mp
        representative.property)
    exact extendedTraceEnergy_comp_le _ contraction contractionBound _

end EIGS

#print axioms EIGS.xiContinuousLpEnergy_normal_contraction
