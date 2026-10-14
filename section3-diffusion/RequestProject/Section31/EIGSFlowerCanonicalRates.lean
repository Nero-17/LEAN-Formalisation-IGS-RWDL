import RequestProject.Section31.EIGSFlowerDistanceSpectrum
import RequestProject.Section31.EIGSFlowerRuleResistance
import RequestProject.Section31.EIGSFlowerMassSpectrum
import RequestProject.Section2ResistanceSpectralRadius

/-! Canonical spectral parameters of the actual flower rule, not an
independent scalar model. -/

namespace EIGS
noncomputable section
open scoped Classical

theorem flowerSystem_distancePositive (branches segments : ℕ)
    (ruleColour edgeColour : Fin 1) :
    ¬ (((flowerSystem branches segments).ruleNetwork ruleColour).withoutColour edgeColour).Reachable
      ((flowerSystem branches segments).plantPlus ruleColour)
      ((flowerSystem branches segments).plantMinus ruleColour) := by
  have colourZero : edgeColour = 0 := Subsingleton.elim _ _
  subst edgeColour
  have graphEmpty : ((flowerSystem branches segments).ruleNetwork ruleColour).withoutColour 0 = ⊥ := by
    ext first second
    simp [Network.withoutColour, flowerSystem, EIGSData.ruleNetwork, flowerGraph]
  rw [graphEmpty, SimpleGraph.reachable_bot]
  exact (flowerSystem branches segments).plant_ne ruleColour

theorem flowerSystem_resistanceSpectralRadius (branches segments : ℕ)
    (branchesPositive : 0 < branches) (segmentsAtLeastTwo : 2 ≤ segments) :
    (flowerSystem branches segments).resistanceSpectralRadius
      (flowerSystem_connected branches segments branchesPositive segmentsAtLeastTwo)
      (flowerSystem_distancePositive branches segments) =
        (segments : ℝ) / (branches : ℝ) := by
  symm
  apply (flowerSystem branches segments).resistanceSpectralRadius_eq_of_positive_eigenpair
    (flowerSystem_connected branches segments branchesPositive segmentsAtLeastTwo)
    (flowerSystem_distancePositive branches segments)
    (div_pos (Nat.cast_pos.mpr (show 0 < segments by omega))
      (Nat.cast_pos.mpr branchesPositive)) (vector := fun _ => 1) (fun _ => zero_lt_one)
  rw [flowerSystem_Psi branches segments branchesPositive segmentsAtLeastTwo _ (fun _ => zero_le_one)]
  funext colour
  simp

theorem flowerSystem_distanceSpectralRadius (branches segments : ℕ)
    (branchesPositive : 0 < branches) (segmentsAtLeastTwo : 2 ≤ segments) :
    (flowerSystem branches segments).distanceSpectralRadius
      (flowerSystem_connected branches segments branchesPositive segmentsAtLeastTwo) = (segments : ℝ) := by
  obtain ⟨lengths, positive, ratePositive, normalized, eigenpair⟩ :=
    (flowerSystem branches segments).metricLengths_spectral_eigenpair
      (flowerSystem_connected branches segments branchesPositive segmentsAtLeastTwo)
      (flowerSystem_loopless branches segments)
      (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo)
      (flowerSystem_distancePositive branches segments)
  rw [flowerSystem_metricLengths branches segments branchesPositive segmentsAtLeastTwo
    lengths (fun colour => (positive colour).le)] at eigenpair
  have coordinate := congrFun eigenpair 0
  simp only [Pi.smul_apply, smul_eq_mul] at coordinate
  have lengthPositive := positive 0
  nlinarith

end
end EIGS

#print axioms EIGS.flowerSystem_distancePositive
#print axioms EIGS.flowerSystem_resistanceSpectralRadius
#print axioms EIGS.flowerSystem_distanceSpectralRadius
