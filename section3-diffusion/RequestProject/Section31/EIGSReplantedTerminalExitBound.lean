import RequestProject.Section31.EIGSReplantedExitDecomposition
import RequestProject.Section31.EIGSReplantedSkeletonReach
import RequestProject.Section2SpectralScaleInequality
import RequestProject.Section2ConcreteSpectralRadius

/-! The actual all-colour, all-start replanted terminal exit estimate.
The strict lower-depth skeleton-reaching bound fills the actual excursion
decomposition, so the recurrence is proved and is not a model assumption.
Only the mass--resistance product must exceed one; resistance may be below one. -/

namespace EIGS

open IGS.Sec31
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))

include rulesLoopless rulesUnique plantingNonadjacent

theorem massResistanceSpectralProduct_gt_one :
    1 < realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive := by
  have distanceLower := system.two_le_distanceSpectralRadius rulesConnected rulesUnique
    plantingNonadjacent distancePositive
  have spectralComparison := system.distanceSpectralRadius_sq_le_mass_mul_resistance
    rulesConnected rulesLoopless rulesUnique distancePositive
  nlinarith [sq_nonneg (system.distanceSpectralRadius rulesConnected - 2)]

theorem xiReplantedTerminalExitMaximum_recursion :
    ∃ increment : ℝ, 0 < increment ∧ ∀ steps,
      xiReplantedTerminalExitMaximum system (steps + 1) ≤
        xiReplantedTerminalExitMaximum system steps + increment *
          (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps := by
  obtain ⟨increment, incrementPositive, decomposition⟩ :=
    xiReplanted_exit_le_first_skeleton_add_spectral_cost system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive
  refine ⟨increment, incrementPositive, ?_⟩
  intro steps
  rw [Nat.add_comm steps 1]
  apply xiReplantedTerminalExitMaximum_le system (1 + steps)
  intro colour vertex
  exact (decomposition colour steps
    (reachBound := xiReplantedTerminalExitMaximum system steps)
    (fun time target => xiReplanted_first_skeleton_partialHit_le_exitMaximum system
      rulesConnected rulesLoopless colour steps time target) vertex).2

theorem xiReplantedTerminalExitMaximum_spectral_upper :
    ∃ upper : ℝ, 0 < upper ∧ ∀ level,
      xiReplantedTerminalExitMaximum system level ≤ upper *
        (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive) ^ level := by
  obtain ⟨increment, incrementPositive, recurrence⟩ :=
    xiReplantedTerminalExitMaximum_recursion system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  have productGap := massResistanceSpectralProduct_gt_one system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive
  refine ⟨increment /
    (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive - 1),
    div_pos incrementPositive (by linarith), ?_⟩
  intro level
  have geometric := geometric_recursion_bound (xiReplantedTerminalExitMaximum system)
    (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive) increment productGap
    incrementPositive.le (xiReplantedTerminalExitMaximum_nonnegative system 0) recurrence level
  simpa only [xiReplantedTerminalExitMaximum_zero, zero_add] using geometric

theorem xiReplantedTerminalExit_spectral_upper :
    ∃ upper : ℝ, 0 < upper ∧ ∀ colour level
      (vertex : XiVtx {system with initCol := colour} level),
      expExit (XiSimpleGraph {system with initCol := colour} level)
        ({xiPositiveTerminal {system with initCol := colour} level,
          xiNegativeTerminal {system with initCol := colour} level} : Finset _)ᶜ vertex ≤
      upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ level := by
  obtain ⟨upper, upperPositive, bound⟩ :=
    xiReplantedTerminalExitMaximum_spectral_upper system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  exact ⟨upper, upperPositive, fun colour level vertex =>
    (xiReplantedTerminalExit_le_maximum system level colour vertex).trans (bound level)⟩

end
end EIGS

#print axioms EIGS.massResistanceSpectralProduct_gt_one
#print axioms EIGS.xiReplantedTerminalExitMaximum_recursion
#print axioms EIGS.xiReplantedTerminalExitMaximum_spectral_upper
#print axioms EIGS.xiReplantedTerminalExit_spectral_upper
