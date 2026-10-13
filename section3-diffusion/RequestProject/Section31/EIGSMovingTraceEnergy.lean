import RequestProject.Section31.EIGSUnitProjectionCoefficients

/-! True coarse trace energies converge even when the boundary coordinates
vary. Convergence of actual conductances and a finite edge sum prove the result;
uniform trace convergence is not supplied as an assumption. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology

set_option maxHeartbeats 2400000

variable {K : ℕ}

theorem xiScaledUnitTraceEnergy_moving_tendsto (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector)))
    (coarseLevel : ℕ) (offsets : ℕ → ℕ) (offsetsTendsto : Tendsto offsets atTop atTop)
    (boundaries : ℕ → XiVtx system coarseLevel → ℝ) (boundaryLimit : XiVtx system coarseLevel → ℝ)
    (boundaryConvergence : Tendsto boundaries atTop (nhds boundaryLimit)) :
    Tendsto (fun index => xiScaledUnitTraceEnergy system rulesConnected resistanceRate normalization
      coarseLevel (offsets index) (boundaries index)) atTop
      (nhds ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive coarseLevel).energy boundaryLimit)) := by
  have edgeConvergence := fun edge : XiEdge system.toRuleData coarseLevel =>
    ((xiTraced_conductance_tendsto_of_normalized_iterate system rulesConnected resistanceRate normalization
      ratePositive normalizationPositive resistanceVector vectorPositive normalizedConvergence coarseLevel
      (XiCol system.toRuleData coarseLevel edge)).comp offsetsTendsto).mul
      ((((continuous_apply (XiTail system coarseLevel edge)).tendsto boundaryLimit).comp boundaryConvergence).sub
        (((continuous_apply (XiHead system coarseLevel edge)).tendsto boundaryLimit).comp boundaryConvergence) |>.pow 2)
  have sumConvergence := tendsto_finset_sum Finset.univ (fun edge _ => edgeConvergence edge)
  simpa only [Function.comp_def, xiScaledUnitTraceEnergy, FiniteNetwork.energy, Network.potentialNetwork,
    xiWeightedFiniteNetwork, XiNetwork, Finset.mul_sum, mul_assoc] using sumConvergence

theorem xiUnitPotentialScaledEnergy_moving_tendsto (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector)))
    (coarseLevel : ℕ) (levels : ℕ → ℕ) (levelsTendsto : Tendsto levels atTop atTop)
    (boundaries : ℕ → XiVtx system coarseLevel → ℝ) (boundaryLimit : XiVtx system coarseLevel → ℝ)
    (boundaryConvergence : Tendsto boundaries atTop (nhds boundaryLimit)) :
    Tendsto (fun index => xiUnitPotentialScaledEnergy system rulesConnected resistanceRate normalization
      coarseLevel (boundaries index) (levels index)) atTop
      (nhds ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive coarseLevel).energy boundaryLimit)) := by
  have traceConvergence := xiScaledUnitTraceEnergy_moving_tendsto system rulesConnected resistanceRate normalization
    ratePositive normalizationPositive resistanceVector vectorPositive normalizedConvergence coarseLevel
    (fun index => levels index - coarseLevel) ((tendsto_sub_atTop_nat coarseLevel).comp levelsTendsto)
    boundaries boundaryLimit boundaryConvergence
  apply traceConvergence.congr'
  filter_upwards [levelsTendsto.eventually (eventually_ge_atTop coarseLevel)] with index afterCoarse
  obtain ⟨offset, levelEquality⟩ := Nat.exists_eq_add_of_le afterCoarse
  rw [levelEquality, Nat.add_sub_cancel_left, xiUnitPotentialScaledEnergy, dif_pos (Nat.le_add_right _ _)]
  exact (xiUnitPotentialAt_scaled_energy system rulesConnected resistanceRate normalization coarseLevel offset (boundaries index)).symm

theorem exists_xiUnitPotentialScaledEnergy_moving_convergence (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour) :
    ∃ normalization : ℝ, 0 < normalization ∧ ∀ coarseLevel
      (levels : ℕ → ℕ), Tendsto levels atTop atTop →
      ∀ (boundaries : ℕ → XiVtx system coarseLevel → ℝ) (boundaryLimit : XiVtx system coarseLevel → ℝ),
      Tendsto boundaries atTop (nhds boundaryLimit) →
      Tendsto (fun index => xiUnitPotentialScaledEnergy system rulesConnected resistanceRate normalization
        coarseLevel (boundaries index) (levels index)) atTop
        (nhds ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive coarseLevel).energy boundaryLimit)) := by
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair
  exact ⟨normalization, normalizationPositive,
    xiUnitPotentialScaledEnergy_moving_tendsto system rulesConnected resistanceRate normalization ratePositive
      normalizationPositive resistanceVector vectorPositive normalizedConvergence⟩

theorem xiNativeBoundaryValues_unit_energy_le (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (mass : XiMassParameters system)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate) (normalizationPositive : 0 < normalization)
    (coarseLevel fineLevel : ℕ) (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass fineLevel)) :
    xiUnitPotentialScaledEnergy system rulesConnected resistanceRate normalization coarseLevel
      (xiNativeBoundaryValues system mass coarseLevel fineLevel values) fineLevel ≤
      xiNativeScaledUnitEnergy system mass resistanceRate normalization fineLevel values := by
  by_cases levelsOrdered : coarseLevel ≤ fineLevel
  · rw [xiUnitPotentialScaledEnergy, dif_pos levelsOrdered]
    apply mul_le_mul_of_nonneg_left _ (mul_pos normalizationPositive (pow_pos ratePositive fineLevel)).le
    apply xiUnitPotentialAt_minimal system rulesConnected coarseLevel fineLevel levelsOrdered
    intro vertex
    simp only [xiNativeBoundaryValues, dif_pos levelsOrdered]
  · rw [xiUnitPotentialScaledEnergy, dif_neg levelsOrdered]
    exact xiNativeScaledUnitEnergy_nonnegative system mass resistanceRate normalization ratePositive.le normalizationPositive.le fineLevel values

end EIGS

#print axioms EIGS.xiScaledUnitTraceEnergy_moving_tendsto
#print axioms EIGS.xiUnitPotentialScaledEnergy_moving_tendsto
#print axioms EIGS.exists_xiUnitPotentialScaledEnergy_moving_convergence
#print axioms EIGS.xiNativeBoundaryValues_unit_energy_le

