import RequestProject.Section31.EIGSNativeClosedCompactness
import RequestProject.Section31.VaryingWeakBounded
import Mathlib.Topology.Order.LiminfLimsup

/-! The genuine weak lower Mosco inequality for the actual varying speed L2
spaces and the constructed extended closed energy. Weak norm boundedness,
compactness, and the energy lower bound are all derived. -/

namespace IGS.Sec31

open Filter Topology
open scoped ENNReal

private theorem extended_energy_le_liminf_of_frequent_sublevels
    (energies : ℕ → ℝ≥0∞) (limitEnergy : ℝ≥0∞)
    (sublevelBound : ∀ bound : ℝ, 0 ≤ bound →
      (∃ᶠ level in atTop, energies level ≤ ENNReal.ofReal bound) → limitEnergy ≤ ENNReal.ofReal bound) :
    limitEnergy ≤ Filter.liminf energies atTop := by
  by_contra contrary
  obtain ⟨bound, aboveLiminf, belowLimit⟩ := exists_between (lt_of_not_ge contrary)
  have boundFinite : bound ≠ ⊤ := (lt_of_lt_of_le belowLimit le_top).ne
  have frequent : ∃ᶠ level in atTop, energies level < bound :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) aboveLiminf
  have boundValid := sublevelBound bound.toReal ENNReal.toReal_nonneg
    (frequent.mono (fun level smaller => by
      rw [ENNReal.ofReal_toReal boundFinite]
      exact smaller.le))
  rw [ENNReal.ofReal_toReal boundFinite] at boundValid
  exact (not_lt_of_ge boundValid) belowLimit

end IGS.Sec31

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology

set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiClosedExtendedEnergy_mosco_lower (system : EIGSData K)
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
    ∀ (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
      (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass)),
      core.Weak sequence target →
      QuadraticEnergySpace.closedExtendedEnergy originalDomain originalForm nonnegative closable target ≤
        Filter.liminf (fun level => ENNReal.ofReal
          (xiNativeScaledUnitEnergy system mass resistanceRate normalization level (sequence level))) atTop := by
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
  intro sequence target weakConvergence
  obtain ⟨normBound, normsBounded⟩ := core.weak_norm_bounded weakConvergence
  apply extended_energy_le_liminf_of_frequent_sublevels
  intro energyBound energyBoundNonnegative frequentBound
  obtain ⟨levels, levelsStrict, energiesBounded⟩ := extraction_forall_of_frequently (fun _ : ℕ => frequentBound)
  obtain ⟨selection, selectionStrict, limit, strongConvergence, limitBound⟩ :=
    exists_xiNativeEnergy_closed_subsequence system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive
      normalizedConvergence levels levelsStrict sequence normBound energyBound (fun index => normsBounded (levels index))
      (fun index => (ENNReal.ofReal_le_ofReal_iff energyBoundNonnegative).1 (energiesBounded index))
  have limitEquality := core.weak_strong_subsequence_limit_eq (levels ∘ selection)
    (levelsStrict.comp selectionStrict).tendsto_atTop sequence target limit weakConvergence strongConvergence
  simpa only [← limitEquality] using limitBound

end EIGS

#print axioms EIGS.xiClosedExtendedEnergy_mosco_lower

