import RequestProject.Section31.EIGSCellExitRecursion

namespace EIGS
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

theorem resistanceSpectralRadius_replanted (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) (colour : Fin K) :
    ({system with initCol := colour} : EIGSData K).resistanceSpectralRadius
      rulesConnected distancePositive = system.resistanceSpectralRadius rulesConnected distancePositive := rfl

/-- One constant controls genuine distinct-skeleton durations for every
initial colour and every further substitution level. This is the duration
input for a local-cell recursion, not its missing jump-count estimate. -/
theorem xiReplantedSkeletonDistinctDuration_spectral_upper (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ colour coarse steps
      (center : XiVtx {system with initCol := colour} coarse),
      xiSkeletonReturnDuration {system with initCol := colour} coarse steps center /
        (1 - xiSkeletonReturnProbability {system with initCol := colour} rulesConnected
          coarse steps center center) ≤
      upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  have perColour := fun colour : Fin K => xiSkeletonDistinctDuration_spectral_upper
    {system with initCol := colour} rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  choose bounds boundsPositive boundsValid using perColour
  have massPositive := (eigs_mass_spectral_growth system rulesConnected distancePositive).1
  have resistancePositive := (system.resistanceSpectralRadius_positive_eigenpair
    rulesConnected distancePositive).1
  refine ⟨Finset.univ.sup' Finset.univ_nonempty bounds,
    (boundsPositive system.initCol).trans_le (Finset.le_sup' bounds (Finset.mem_univ _)), ?_⟩
  intro colour coarse steps center
  apply (boundsValid colour coarse steps center).trans
  exact mul_le_mul_of_nonneg_right (Finset.le_sup' bounds (Finset.mem_univ colour))
    (pow_nonneg (mul_nonneg massPositive.le resistancePositive.le) steps)

end
end EIGS

#print axioms EIGS.resistanceSpectralRadius_replanted
#print axioms EIGS.xiReplantedSkeletonDistinctDuration_spectral_upper
