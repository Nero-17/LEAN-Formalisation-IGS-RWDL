import RequestProject.Section31.EIGSFullMosco
import RequestProject.Section31.VaryingWeakBounded
import Mathlib.Topology.Order.LiminfLimsup

/-! Native varying-space lower bounds along arbitrary strict original levels.
The proof constructs norm bounds and genuine strong subsubsequences using the
accepted actual compactness theorem, then identifies their limits with the
selected weak limit. Selected-level Mosco convergence is not assumed. -/

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

theorem xiClosedExtendedEnergy_selected_mosco_lower (system : EIGSData K)
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
    ∀ (levels : ℕ → ℕ) (levelsStrict : StrictMono levels)
      (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
      (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass)),
      (core.reindex levels levelsStrict.tendsto_atTop).Weak
        (fun index => sequence (levels index)) target →
      QuadraticEnergySpace.closedExtendedEnergy originalDomain originalForm nonnegative closable target ≤
        Filter.liminf (fun index => ENNReal.ofReal
          (xiNativeScaledUnitEnergy system mass resistanceRate normalization (levels index) (sequence (levels index)))) atTop := by
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
  intro levels levelsStrict sequence target weakConvergence
  obtain ⟨normBound, normsBounded⟩ :=
    (core.reindex levels levelsStrict.tendsto_atTop).weak_norm_bounded weakConvergence
  apply extended_energy_le_liminf_of_frequent_sublevels
  intro energyBound energyBoundNonnegative frequentBound
  obtain ⟨indices, indicesStrict, energiesBounded⟩ :=
    extraction_forall_of_frequently (fun _ : ℕ => frequentBound)
  obtain ⟨selection, selectionStrict, limit, strongConvergence, limitBound⟩ :=
    exists_xiNativeEnergy_closed_subsequence system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive
      normalizedConvergence (levels ∘ indices) (levelsStrict.comp indicesStrict) sequence normBound energyBound
      (fun index => normsBounded (indices index))
      (fun index => (ENNReal.ofReal_le_ofReal_iff energyBoundNonnegative).1 (energiesBounded index))
  have selectedStrong :
      ((core.reindex levels levelsStrict.tendsto_atTop).reindex (indices ∘ selection)
        (indicesStrict.comp selectionStrict).tendsto_atTop).Strong
        (fun index => sequence (levels (indices (selection index)))) limit := by
    simpa only [VaryingHilbertCore.reindex, Function.comp_def] using strongConvergence
  have limitEquality :=
    (core.reindex levels levelsStrict.tendsto_atTop).weak_strong_subsequence_limit_eq
      (indices ∘ selection) (indicesStrict.comp selectionStrict).tendsto_atTop
      (fun index => sequence (levels index)) target limit weakConvergence selectedStrong
  simpa only [← limitEquality] using limitBound

theorem exists_xiSelectedMoscoLower_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
        (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, 0 < normalization ∧
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive
      let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
        intro sequence energyCauchy ambientZero
        exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
          mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
          (by simpa using ambientZero.norm)
      (∀ (levels : ℕ → ℕ) (levelsStrict : StrictMono levels)
        (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass)),
        (core.reindex levels levelsStrict.tendsto_atTop).Weak (fun index => sequence (levels index)) target →
        QuadraticEnergySpace.closedExtendedEnergy originalDomain originalForm nonnegative closable target ≤
          Filter.liminf (fun index => ENNReal.ofReal
            (xiNativeScaledUnitEnergy system mass resistanceRate normalization (levels index) (sequence (levels index)))) atTop) := by
  classical
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceVector, resistanceRate, vectorPositive, ratePositive, _, eigenpair⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_eigenpair coloursPositive distancePositive
  have renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour :=
    fun colour => congrFun eigenpair colour
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiClosedExtendedEnergy_selected_mosco_lower system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence

end EIGS

#print axioms EIGS.xiClosedExtendedEnergy_selected_mosco_lower


#print axioms EIGS.exists_xiSelectedMoscoLower_of_rules
