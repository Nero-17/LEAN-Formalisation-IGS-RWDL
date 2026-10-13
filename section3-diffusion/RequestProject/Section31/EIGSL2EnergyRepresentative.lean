import RequestProject.Section31.EIGSAddressSupport
import RequestProject.Section31.EIGSLimitEnergy
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Full support makes continuous representatives unique in the actual limit
Lp space. The concrete finite-energy continuous domain therefore has a
well-defined image in L². No closedness or Mosco property is claimed here. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped ENNReal

variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system)

noncomputable def xiContinuousL2Map :
    C(XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair, ℝ) →L[ℝ]
    Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass) :=
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  ContinuousMap.toLp 2 (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass) ℝ

theorem xiContinuousL2Map_injective :
    Function.Injective (xiContinuousL2Map system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass) := by
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  exact ContinuousMap.toLp_injective _

noncomputable def xiContinuousUnionRestriction :
    C(XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair, ℝ) →ₗ[ℝ] (XiVertexUnion system → ℝ) where
  toFun function := function ∘ xiCompletionUnionEmbedding system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

noncomputable def xiContinuousFiniteEnergyDomain
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour) :
    Submodule ℝ C(XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair, ℝ) :=
  (xiWeightedEnergyDomain system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive).comap
    (xiContinuousUnionRestriction system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)

noncomputable def xiContinuousEnergyLpDomain
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour) :
    Submodule ℝ (Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)) :=
  (xiContinuousFiniteEnergyDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
    resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive).map
      (xiContinuousL2Map system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).toLinearMap

theorem xiContinuousEnergyLpDomain_mem
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (function : C(XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair, ℝ)) :
    xiContinuousL2Map system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass function ∈
      xiContinuousEnergyLpDomain system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive ↔
    xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      (function ∘ xiCompletionUnionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair) ≠ ∞ := by
  constructor
  · rintro ⟨other, otherFinite, sameClass⟩
    have equality : other = function := xiContinuousL2Map_injective system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass sameClass
    subst other
    exact (xiWeightedEnergyDomain_iff system resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive _).mp otherFinite
  · intro energyFinite
    refine ⟨function, ?_, rfl⟩
    exact (xiWeightedEnergyDomain_iff system resistanceRate resistanceRatePositive
      resistanceVector resistanceVectorPositive _).mpr energyFinite

theorem xiContinuous_extended_energy_of_same_L2
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (first second : C(XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair, ℝ))
    (sameClass : xiContinuousL2Map system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass first =
      xiContinuousL2Map system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass second) :
    xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      (first ∘ xiCompletionUnionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair) =
    xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      (second ∘ xiCompletionUnionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair) := by
  rw [xiContinuousL2Map_injective system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass sameClass]

end EIGS

#print axioms EIGS.xiContinuousL2Map_injective
#print axioms EIGS.xiContinuousEnergyLpDomain_mem
#print axioms EIGS.xiContinuous_extended_energy_of_same_L2
