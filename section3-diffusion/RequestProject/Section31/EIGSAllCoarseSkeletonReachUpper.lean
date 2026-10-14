import RequestProject.Section31.EIGSReplantedTerminalExitBound

/-! Every fine starting vertex reaches an arbitrary coarse skeleton within
the actual uniform replanted cell terminal-exit bound. This is a finite
mean-hitting estimate, not a continuous mean-exit assertion. Candidate source. -/

namespace EIGS
open IGS.Sec31
open scoped Classical
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

theorem xiAllCoarseSkeleton_partialHit_le_replantedMaximum (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (coarse steps time : ℕ) (vertex : XiVtx system (coarse + steps)) :
    partialHit (xiGraphWalkChain system rulesConnected (coarse + steps))
      (Finset.univ.image (xiForward system coarse steps)) time vertex ≤
        xiReplantedTerminalExitMaximum system steps := by
  cases steps with
  | zero =>
      have member : vertex ∈ Finset.univ.image (xiForward system coarse 0) :=
        Finset.mem_image.mpr ⟨vertex, Finset.mem_univ _, rfl⟩
      rw [partialHit_zero_on_boundary _ _ member]
      exact xiReplantedTerminalExitMaximum_nonnegative system 0
  | succ level =>
      have degree : ∀ target, 0 < (XiNetwork system (coarse + (level + 1))).toSimpleGraph.degree target := by
        intro target
        exact_mod_cast xiSimpleGraph_degree_positive system rulesConnected (coarse + (level + 1)) target
      have ambientDegree : ∀ target,
          0 < (((XiNetwork system coarse).subst (system.ruleFamily rulesConnected)).substIter
            (system.ruleFamily rulesConnected) level).toSimpleGraph.degree target := by
        have positive := degree
        rw [xiNetwork_succ_substIter system rulesConnected coarse level] at positive
        exact positive
      have comparison := Network.graphWalk_partialHit_cast
        (xiNetwork_succ_substIter system rulesConnected coarse level).symm
        ambientDegree degree
        ((XiNetwork system coarse).iteratedSubstitutionSkeleton (system.ruleFamily rulesConnected) level)
        time ((Network.castVertex (xiNetwork_succ_substIter system rulesConnected coarse level).symm).symm vertex)
      have skeleton := xiNetwork_succ_substIter_skeleton system rulesConnected coarse level
      change ((XiNetwork system coarse).iteratedSubstitutionSkeleton (system.ruleFamily rulesConnected) level).image
        (Network.castVertex (xiNetwork_succ_substIter system rulesConnected coarse level).symm) =
          Finset.univ.image (xiForward system coarse (level + 1)) at skeleton
      rw [Equiv.apply_symm_apply, skeleton] at comparison
      simpa only [Nat.add_comm 1 level] using
        comparison.le.trans (Network.skeleton_partialHit_le_replantedMaximum system rulesConnected
          (XiNetwork system coarse) (xiNetwork_loopless system rulesConnected rulesLoopless coarse)
          level ambientDegree time _)

theorem xiAllCoarseSkeleton_partialHit_spectral_upper (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse steps time (vertex : XiVtx system (coarse + steps)),
      partialHit (xiGraphWalkChain system rulesConnected (coarse + steps))
        (Finset.univ.image (xiForward system coarse steps)) time vertex ≤
        upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps := by
  obtain ⟨upper, upperPositive, bounds⟩ := xiReplantedTerminalExitMaximum_spectral_upper
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  exact ⟨upper, upperPositive, fun coarse steps time vertex =>
    (xiAllCoarseSkeleton_partialHit_le_replantedMaximum system rulesConnected rulesLoopless
      coarse steps time vertex).trans (bounds steps)⟩

end
end EIGS

#print axioms EIGS.xiAllCoarseSkeleton_partialHit_le_replantedMaximum
#print axioms EIGS.xiAllCoarseSkeleton_partialHit_spectral_upper
