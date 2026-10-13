import RequestProject.Section31.EIGSMesoscopicTrace

/-! Actual original-unit harmonic energies, with their original-level Perron
normalization, converge to the constructed stationary harmonic energy. -/

namespace EIGS

open Filter Topology

set_option maxHeartbeats 1800000

variable {K : ℕ}

theorem xiUnitPotentialAt_eq_potentialValues (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (initialLevel offset : ℕ) (initialValues : XiVtx system initialLevel → ℝ) :
    xiUnitPotentialAt system rulesConnected initialLevel (initialLevel + offset) (Nat.le_add_right _ _) initialValues =
      xiPotentialValues system rulesConnected initialLevel offset (fun _ => 1) (fun _ => by norm_num) initialValues := by
  apply xiPotentialValues_unique system rulesConnected initialLevel offset (fun _ => 1) (fun _ => by norm_num)
  · intro vertex
    rw [← xiVertexInclusion_eq_forward, xiUnitPotentialAt_boundary]
  · intro competitor competitorBoundary
    apply xiUnitPotentialAt_minimal system rulesConnected initialLevel (initialLevel + offset) (Nat.le_add_right _ _) initialValues
    intro vertex
    rw [xiVertexInclusion_eq_forward]
    exact competitorBoundary vertex

theorem xiUnitPotentialAt_scaled_energy (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (initialLevel offset : ℕ)
    (initialValues : XiVtx system initialLevel → ℝ) :
    xiScaledUnitEnergy system resistanceRate normalization (initialLevel + offset)
      (xiUnitPotentialAt system rulesConnected initialLevel (initialLevel + offset) (Nat.le_add_right _ _) initialValues) =
      xiScaledUnitTraceEnergy system rulesConnected resistanceRate normalization initialLevel offset initialValues := by
  rw [xiScaledUnitEnergy, xiScaledUnitTraceEnergy, xiUnitPotentialAt_eq_potentialValues, xiPotentialValues_energy]

noncomputable def xiUnitPotentialScaledEnergy (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (initialLevel : ℕ)
    (initialValues : XiVtx system initialLevel → ℝ) (level : ℕ) : ℝ :=
  if afterInitial : initialLevel ≤ level then
    xiScaledUnitEnergy system resistanceRate normalization level
      (xiUnitPotentialAt system rulesConnected initialLevel level afterInitial initialValues)
  else 0

theorem xiUnitPotentialScaledEnergy_tendsto (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector)))
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ) :
    Tendsto (xiUnitPotentialScaledEnergy system rulesConnected resistanceRate normalization initialLevel initialValues)
      atTop (nhds ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive initialLevel).energy
        initialValues)) := by
  apply (tendsto_add_atTop_iff_nat initialLevel).1
  have traceConvergence := xiScaledUnitTraceEnergy_tendsto_of_normalized_iterate system rulesConnected resistanceRate normalization
    ratePositive normalizationPositive resistanceVector vectorPositive normalizedConvergence initialLevel initialValues
  apply traceConvergence.congr
  intro offset
  change xiScaledUnitTraceEnergy system rulesConnected resistanceRate normalization initialLevel offset initialValues =
    xiUnitPotentialScaledEnergy system rulesConnected resistanceRate normalization initialLevel initialValues (offset + initialLevel)
  rw [Nat.add_comm offset initialLevel, xiUnitPotentialScaledEnergy, dif_pos (Nat.le_add_right _ _)]
  exact (xiUnitPotentialAt_scaled_energy system rulesConnected resistanceRate normalization initialLevel offset initialValues).symm

end EIGS
