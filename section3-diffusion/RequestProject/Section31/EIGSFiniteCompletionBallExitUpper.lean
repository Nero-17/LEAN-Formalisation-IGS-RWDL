import RequestProject.Section31.EIGSTwoStarAllSourceExitUpper
import RequestProject.Section31.EIGSFineBallTwoStarContainment

/-! Genuine finite expected exit from completion balls. The geometric
containment is proved for every fine center; the comparison domain has
two coarse endpoints and the actual skeleton jump bound. -/

namespace EIGS
open IGS.Sec31
open scoped Classical
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

theorem xiFiniteCompletionBall_allSource_expExit_spectral_upper (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = rate • lengths)
    (lowerLength : ℝ) (lowerLengthPositive : 0 < lowerLength)
    (lengthLower : ∀ colour, lowerLength ≤ lengths colour) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse, 1 ≤ coarse → ∀ steps
      (center source : XiVtx system (coarse + steps)),
      expExit (XiSimpleGraph system (coarse + steps))
        (Finset.univ.filter fun target =>
          dist (xiCompletionEmbedding system rulesConnected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarse + steps) center)
            (xiCompletionEmbedding system rulesConnected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarse + steps) target) <
            lowerLength * rate⁻¹ ^ coarse) source ≤
        upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps := by
  obtain ⟨upper, upperPositive, bounds⟩ :=
    xiTwoPointCoarseGroundedDomain_allSource_expExit_spectral_upper system rulesConnected
      rulesLoopless rulesUnique plantingNonadjacent distancePositive
  refine ⟨upper, upperPositive, ?_⟩
  intro coarse coarsePositive steps center source
  obtain ⟨selected, contained⟩ := xiCompletionFineBall_subset_two_stars system rulesConnected
    lengths lengthsPositive rate rateGreaterThanOne eigenpair lowerLength lowerLengthPositive
    lengthLower coarse steps center
  have adjacent : (XiSimpleGraph system coarse).Adj
      (XiTail system coarse selected) (XiHead system coarse selected) := by
    exact ⟨xiNetwork_loopless system rulesConnected rulesLoopless coarse selected,
      Or.inl ⟨selected, rfl, rfl⟩⟩
  obtain ⟨endpoint, exterior, _, exteriorTail, exteriorHead, _⟩ :=
    xiPositiveCoarse_pair_has_exterior_neighbor system rulesConnected plantingNonadjacent
      coarse coarsePositive (XiTail system coarse selected) (XiHead system coarse selected)
  have proper : (xiTwoPointCoarseGroundedDomain system coarse steps
      (XiTail system coarse selected) (XiHead system coarse selected))ᶜ.Nonempty := by
    refine ⟨xiForward system coarse steps exterior, Finset.mem_compl.mpr ?_⟩
    intro inside
    have outside := (Finset.mem_sdiff.mp inside).2
    apply outside
    exact Finset.mem_image.mpr ⟨exterior, by simp [exteriorTail, exteriorHead], rfl⟩
  apply (expExit_mono_domain (xiSimpleGraph_connected system rulesConnected (coarse + steps))
    (outside := xiTwoPointCoarseGroundedDomain system coarse steps
      (XiTail system coarse selected) (XiHead system coarse selected)) ?_ proper source).trans
    (bounds coarse coarsePositive steps _ _ adjacent source)
  intro target inside
  apply xiTwoIncidentStars_subset_grounded_pair system coarse steps
    (XiTail system coarse selected) (XiHead system coarse selected)
  rcases contained target (Finset.mem_filter.mp inside).2 with tailStar | headStar
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, tailStar⟩))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, headStar⟩))

end
end EIGS

#print axioms EIGS.xiFiniteCompletionBall_allSource_expExit_spectral_upper
