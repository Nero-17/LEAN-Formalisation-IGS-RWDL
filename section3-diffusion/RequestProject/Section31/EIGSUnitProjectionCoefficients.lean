import RequestProject.Section31.EIGSUnitHarmonicCoercivity
import RequestProject.Section31.EIGSNativeProjectionTailOfRules
import RequestProject.Section31.VaryingProjectionCompactness

/-! The actual coarse boundary coordinates of bounded native-energy sequences
are bounded, and all coarse levels admit one common convergent subsequence. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BigOperators

variable {K : ℕ}

noncomputable def xiNativeBoundaryValues (system : EIGSData K) (mass : XiMassParameters system)
    (coarseLevel fineLevel : ℕ) (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass fineLevel)) :
    XiVtx system coarseLevel → ℝ :=
  if levelsOrdered : coarseLevel ≤ fineLevel then
    fun vertex => values (xiVertexInclusion system coarseLevel fineLevel levelsOrdered vertex)
  else 0

theorem xiNativeBoundaryValues_projection_eq (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (mass : XiMassParameters system)
    (coarseLevel fineLevel : ℕ) (levelsOrdered : coarseLevel ≤ fineLevel)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass fineLevel)) :
    xiUnitNativeL2 system rulesConnected mass coarseLevel (xiNativeBoundaryValues system mass coarseLevel fineLevel values) fineLevel =
      xiFiniteSpeedL2 system mass fineLevel
        (xiUnitEnergyProjection system rulesConnected coarseLevel fineLevel levelsOrdered (fun vertex => values vertex)) := by
  rw [xiUnitNativeL2_at_level system rulesConnected mass coarseLevel fineLevel levelsOrdered,
    xiUnitEnergyProjection_eq_potentialAt]
  simp only [xiNativeBoundaryValues, dif_pos levelsOrdered]

theorem exists_xiNativeBoundaryValues_bound (system : EIGSData K)
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
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (levels : ℕ → ℕ) (levelsTendsto : Tendsto levels atTop atTop)
    (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (normBound energyBound : ℝ) (normsBounded : ∀ index, ‖sequence (levels index)‖ ≤ normBound)
    (energiesBounded : ∀ index, xiNativeScaledUnitEnergy system mass resistanceRate normalization (levels index) (sequence (levels index)) ≤ energyBound)
    (coarseLevel : ℕ) :
    ∃ bound : ℝ, ∀ fineLevel,
      ‖xiNativeBoundaryValues system mass coarseLevel (levels fineLevel) (sequence (levels fineLevel))‖ ≤ bound := by
  obtain ⟨inverseConstant, inversePositive, inverseBound⟩ := exists_xiUnitHarmonic_eventual_coercivity system rulesConnected
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass distancePositive oneColourDistance
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair coarseLevel
  obtain ⟨tailConstant, tailPositive, tailBound⟩ := exists_xiUnitProjection_native_tail_for_eigenpair system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive mass resistanceRate ratePositive resistanceVector vectorPositive
    eigenpair normalization normalizationPositive
  have normBoundNonnegative : 0 ≤ normBound := (norm_nonneg (sequence (levels 0))).trans (normsBounded 0)
  have eventualBound : ∀ᶠ fineLevel in atTop,
      ‖xiNativeBoundaryValues system mass coarseLevel (levels fineLevel) (sequence (levels fineLevel))‖ ≤
      inverseConstant * (normBound + tailConstant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ coarseLevel *
        Real.sqrt energyBound) := by
    filter_upwards [levelsTendsto.eventually inverseBound, levelsTendsto.eventually (eventually_ge_atTop coarseLevel)] with fineLevel inverseBound levelsOrdered
    have actualTail := tailBound coarseLevel (levels fineLevel) levelsOrdered (fun vertex => sequence (levels fineLevel) vertex)
    rw [xiFiniteSpeedL2_representative, xiUnitEnergyProjection_eq_potentialAt] at actualTail
    have rowEquality : xiUnitNativeL2 system rulesConnected mass coarseLevel
        (xiNativeBoundaryValues system mass coarseLevel (levels fineLevel) (sequence (levels fineLevel))) (levels fineLevel) =
        xiFiniteSpeedL2 system mass (levels fineLevel)
          (xiUnitPotentialAt system rulesConnected coarseLevel (levels fineLevel) levelsOrdered
            (fun vertex => sequence (levels fineLevel) (xiVertexInclusion system coarseLevel (levels fineLevel) levelsOrdered vertex))) := by
      rw [xiUnitNativeL2_at_level system rulesConnected mass coarseLevel (levels fineLevel) levelsOrdered]
      simp only [xiNativeBoundaryValues, dif_pos levelsOrdered]
    rw [← rowEquality] at actualTail
    have rootBound := Real.sqrt_le_sqrt (energiesBounded fineLevel)
    have projectionBound : ‖xiUnitNativeL2 system rulesConnected mass coarseLevel
        (xiNativeBoundaryValues system mass coarseLevel (levels fineLevel) (sequence (levels fineLevel))) (levels fineLevel)‖ ≤
        normBound + tailConstant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ coarseLevel * Real.sqrt energyBound := by
      calc
        _ ≤ ‖sequence (levels fineLevel)‖ +
            ‖sequence (levels fineLevel) - xiUnitNativeL2 system rulesConnected mass coarseLevel
              (xiNativeBoundaryValues system mass coarseLevel (levels fineLevel) (sequence (levels fineLevel))) (levels fineLevel)‖ := by
          calc
            _ = ‖sequence (levels fineLevel) - (sequence (levels fineLevel) - xiUnitNativeL2 system rulesConnected mass coarseLevel
                (xiNativeBoundaryValues system mass coarseLevel (levels fineLevel) (sequence (levels fineLevel))) (levels fineLevel))‖ := by rw [sub_sub_cancel]
            _ ≤ _ := norm_sub_le _ _
        _ ≤ normBound + tailConstant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ coarseLevel * Real.sqrt energyBound :=
          add_le_add (normsBounded fineLevel) (actualTail.trans
            (mul_le_mul_of_nonneg_left rootBound
              (mul_nonneg tailPositive.le (pow_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) coarseLevel))))
    exact (inverseBound _).trans (mul_le_mul_of_nonneg_left projectionBound inversePositive.le)
  obtain ⟨threshold, afterThreshold⟩ := eventually_atTop.1 eventualBound
  refine ⟨inverseConstant * (normBound + tailConstant * (Real.sqrt (mass.rate * resistanceRate))⁻¹ ^ coarseLevel *
      Real.sqrt energyBound) +
      ∑ level ∈ Finset.range threshold, ‖xiNativeBoundaryValues system mass coarseLevel (levels level) (sequence (levels level))‖, ?_⟩
  intro fineLevel
  have prefixNonnegative : 0 ≤ ∑ level ∈ Finset.range threshold,
      ‖xiNativeBoundaryValues system mass coarseLevel (levels level) (sequence (levels level))‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  by_cases after : threshold ≤ fineLevel
  · exact (afterThreshold fineLevel after).trans (le_add_of_nonneg_right prefixNonnegative)
  · have prefixBound := Finset.single_le_sum (fun level (_ : level ∈ Finset.range threshold) =>
      norm_nonneg (xiNativeBoundaryValues system mass coarseLevel (levels level) (sequence (levels level))))
      (Finset.mem_range.2 (Nat.lt_of_not_ge after))
    exact prefixBound.trans (le_add_of_nonneg_left (by positivity))

theorem exists_xiNativeBoundaryValues_common_subsequence (system : EIGSData K)
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
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (levels : ℕ → ℕ) (levelsTendsto : Tendsto levels atTop atTop)
    (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (normBound energyBound : ℝ) (normsBounded : ∀ index, ‖sequence (levels index)‖ ≤ normBound)
    (energiesBounded : ∀ index, xiNativeScaledUnitEnergy system mass resistanceRate normalization (levels index) (sequence (levels index)) ≤ energyBound) :
    ∃ limits : ∀ coarseLevel, XiVtx system coarseLevel → ℝ, ∃ selection : ℕ → ℕ,
      StrictMono selection ∧ ∀ coarseLevel,
      Tendsto (fun index => xiNativeBoundaryValues system mass coarseLevel (levels (selection index)) (sequence (levels (selection index))))
        atTop (nhds (limits coarseLevel)) := by
  apply IGS.Sec31.bounded_coordinates_common_subsequence (fun coarseLevel => XiVtx system coarseLevel → ℝ)
    (fun coarseLevel fineLevel => xiNativeBoundaryValues system mass coarseLevel (levels fineLevel) (sequence (levels fineLevel)))
  exact exists_xiNativeBoundaryValues_bound system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive levels levelsTendsto sequence
    normBound energyBound normsBounded energiesBounded

end EIGS

#print axioms EIGS.xiNativeBoundaryValues
#print axioms EIGS.xiNativeBoundaryValues_projection_eq
#print axioms EIGS.exists_xiNativeBoundaryValues_bound
#print axioms EIGS.exists_xiNativeBoundaryValues_common_subsequence
