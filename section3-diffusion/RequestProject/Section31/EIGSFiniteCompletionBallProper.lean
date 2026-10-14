import RequestProject.Section31.EIGSTwoStarAllSourceExitUpper
import RequestProject.Section31.EIGSFineBallTwoStarContainment

namespace EIGS
open IGS.Sec31
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem xiFiniteCompletionBall_complement_nonempty (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (lowerLength : ℝ) (lowerLengthPositive : 0 < lowerLength)
    (lengthLower : ∀ colour, lowerLength ≤ lengths colour)
    (coarse : ℕ) (coarsePositive : 1 ≤ coarse) (steps : ℕ)
    (center : XiVtx system (coarse + steps)) :
    (Finset.univ.filter fun target =>
      dist (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarse + steps) center)
        (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarse + steps) target) <
        lowerLength * rate⁻¹ ^ coarse)ᶜ.Nonempty := by
  obtain ⟨selected, contained⟩ := xiCompletionFineBall_subset_two_stars system connected
    lengths lengthsPositive rate rateGreaterThanOne eigenpair lowerLength lowerLengthPositive
    lengthLower coarse steps center
  obtain ⟨endpoint, exterior, _, exteriorTail, exteriorHead, _⟩ :=
    xiPositiveCoarse_pair_has_exterior_neighbor system connected plantingNonadjacent
      coarse coarsePositive (XiTail system coarse selected) (XiHead system coarse selected)
  refine ⟨xiForward system coarse steps exterior, Finset.mem_compl.mpr ?_⟩
  intro inside
  have inGrounded : xiForward system coarse steps exterior ∈
      xiTwoPointCoarseGroundedDomain system coarse steps
        (XiTail system coarse selected) (XiHead system coarse selected) := by
    apply xiTwoIncidentStars_subset_grounded_pair system coarse steps
      (XiTail system coarse selected) (XiHead system coarse selected)
    rcases contained _ (Finset.mem_filter.mp inside).2 with tailStar | headStar
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, tailStar⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, headStar⟩))
  apply (Finset.mem_sdiff.mp inGrounded).2
  exact Finset.mem_image.mpr ⟨exterior, by simp [exteriorTail, exteriorHead], rfl⟩

end
end EIGS

#print axioms EIGS.xiFiniteCompletionBall_complement_nonempty
