import RequestProject.Section31.EIGSAllStartSkeletonExit
import RequestProject.Section31.EIGSCellStarExit
import RequestProject.Section2StarExitLower
import RequestProject.Section2SurvivalFromExit

namespace EIGS
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem xiIncidentStarDomain_erased_subset_skeleton_complement (system : EIGSData K)
    (coarse steps : ℕ) (center : XiVtx system coarse) :
    (xiIncidentStarDomain system coarse steps center).erase (xiForward system coarse steps center) ⊆
      (Finset.univ.image (xiForward system coarse steps))ᶜ := by
  intro vertex membership
  apply Finset.mem_compl.mpr
  intro inSkeleton
  obtain ⟨original, _, rfl⟩ := Finset.mem_image.mp inSkeleton
  have same := (xiIncidentStar_forward_iff system coarse steps center original).mp
    (Finset.mem_filter.mp (Finset.mem_erase.mp membership).2).2
  exact (Finset.mem_erase.mp membership).1 (congrArg (xiForward system coarse steps) same)

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))

include rulesLoopless rulesUnique plantingNonadjacent

/-- Every point of every actual incident star has a uniform exit mean.
The center estimate and the time to the whole coarse skeleton are proved
from the rules before this comparison is applied. -/
theorem xiIncidentStarDomain_all_start_expExit_spectral_upper :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse steps (center : XiVtx system coarse)
      (vertex : XiVtx system (coarse + steps)),
      expExit (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center) vertex ≤
      upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps := by
  obtain ⟨skeletonUpper, skeletonPositive, skeletonBound⟩ :=
    xiSkeleton_expExit_spectral_upper system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  obtain ⟨centerUpper, centerPositive, centerBound⟩ :=
    xiIncidentStarDomain_expExit_spectral_upper system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨skeletonUpper + centerUpper, add_pos skeletonPositive centerPositive, ?_⟩
  intro coarse steps center vertex
  have proper : ((Finset.univ.image (xiForward system coarse steps))ᶜ)ᶜ.Nonempty := by
    rw [compl_compl]
    exact ⟨xiForward system coarse steps (xiPositiveTerminal system coarse),
      Finset.mem_image.mpr ⟨xiPositiveTerminal system coarse, Finset.mem_univ _, rfl⟩⟩
  have erasedBound := expExit_mono_domain
    (xiSimpleGraph_connected system rulesConnected (coarse + steps))
    (xiIncidentStarDomain_erased_subset_skeleton_complement system coarse steps center) proper vertex
  calc
    _ ≤ expExit (XiSimpleGraph system (coarse + steps))
          ((xiIncidentStarDomain system coarse steps center).erase
            (xiForward system coarse steps center)) vertex +
        expExit (XiSimpleGraph system (coarse + steps))
          (xiIncidentStarDomain system coarse steps center) (xiForward system coarse steps center) :=
      xiIncidentStarDomain_expExit_le_erased_add_center system rulesConnected coarse steps center vertex
    _ ≤ skeletonUpper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps +
        centerUpper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps :=
      add_le_add (erasedBound.trans (skeletonBound coarse steps vertex)) (centerBound coarse steps center)
    _ = _ := by ring

/-- At every coarse center there is a common positive chance of remaining
in its actual star for a fixed fraction of the spectral time scale. This
is a finite-time survival statement, not yet a stopping-time assertion. -/
theorem xiIncidentStarDomain_uniform_positive_survival :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ coarse steps (center : XiVtx system coarse) (time : ℕ),
      (time : ℝ) ≤ lower * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps / 2 →
      lower / (2 * upper) ≤ surv (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center) time (xiForward system coarse steps center) := by
  obtain ⟨upper, upperPositive, upperBound⟩ :=
    xiIncidentStarDomain_all_start_expExit_spectral_upper system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive
  obtain ⟨lower, lowerPositive, lowerBound⟩ :=
    xiIncidentStarDomain_expExit_spectral_lower system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨lower, upper, lowerPositive, upperPositive, ?_⟩
  intro coarse steps center time timeBound
  apply survival_uniform_positive_of_exit_bounds (XiSimpleGraph system (coarse + steps))
    (xiSimpleGraph_connected system rulesConnected (coarse + steps))
    (xiIncidentStarDomain_complement_nonempty system coarse steps center)
    lower upper _ upperPositive
    (pow_pos (mul_pos (eigs_mass_spectral_growth system rulesConnected distancePositive).1
      (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1) steps)
    (upperBound coarse steps center) time (xiForward system coarse steps center)
    (lowerBound coarse steps center) timeBound

end
end EIGS

#print axioms EIGS.xiIncidentStarDomain_erased_subset_skeleton_complement
#print axioms EIGS.xiIncidentStarDomain_all_start_expExit_spectral_upper
#print axioms EIGS.xiIncidentStarDomain_uniform_positive_survival
