import RequestProject.Section31.EIGSReplantedTerminalExitBound

/-! Every coarse level and every fine starting vertex satisfy the actual
skeleton exit bound. Child localization supplies the lower-depth maximum;
the all-colour terminal recursion then supplies its spectral estimate. -/

namespace EIGS

open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

theorem xiSkeleton_partialHit_le_replantedMaximum (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (coarse steps time : ℕ) (vertex : XiVtx system (coarse + steps)) :
    IGS.Sec31.partialHit (xiGraphWalkChain system rulesConnected (coarse + steps))
        (Finset.univ.image (xiForward system coarse steps)) time vertex ≤
      xiReplantedTerminalExitMaximum system steps := by
  cases steps with
  | zero =>
      have member : vertex ∈ Finset.univ.image (xiForward system coarse 0) :=
        Finset.mem_image.mpr ⟨vertex, Finset.mem_univ _, rfl⟩
      rw [IGS.Sec31.partialHit_zero_on_boundary _ _ member]
      exact xiReplantedTerminalExitMaximum_nonnegative system 0
  | succ level =>
      have degree : ∀ vertex,
          0 < (XiNetwork system (coarse + (level + 1))).toSimpleGraph.degree vertex := by
        intro vertex
        exact_mod_cast xiSimpleGraph_degree_positive system rulesConnected (coarse + (level + 1)) vertex
      have ambient_degree : ∀ vertex,
          0 < (((XiNetwork system coarse).subst (system.ruleFamily rulesConnected)).substIter
            (system.ruleFamily rulesConnected) level).toSimpleGraph.degree vertex := by
        have positive := degree
        rw [xiNetwork_succ_substIter system rulesConnected coarse level] at positive
        exact positive
      have comparison := Network.graphWalk_partialHit_cast
        (xiNetwork_succ_substIter system rulesConnected coarse level).symm
        ambient_degree degree
        ((XiNetwork system coarse).iteratedSubstitutionSkeleton (system.ruleFamily rulesConnected) level) time
        ((Network.castVertex (xiNetwork_succ_substIter system rulesConnected coarse level).symm).symm vertex)
      rw [Equiv.apply_symm_apply,
        xiNetwork_succ_substIter_skeleton system rulesConnected coarse level] at comparison
      simpa only [Nat.add_comm 1 level] using
        (comparison.le.trans (Network.skeleton_partialHit_le_replantedMaximum system rulesConnected
          (XiNetwork system coarse) (xiNetwork_loopless system rulesConnected rulesLoopless coarse)
          level ambient_degree time _))

theorem xiSkeleton_expExit_le_replantedMaximum (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (coarse steps : ℕ) (vertex : XiVtx system (coarse + steps)) :
    expExit (XiSimpleGraph system (coarse + steps))
        (Finset.univ.image (xiForward system coarse steps))ᶜ vertex ≤
      xiReplantedTerminalExitMaximum system steps := by
  have nonempty : (Finset.univ.image (xiForward system coarse steps)).Nonempty :=
    ⟨xiForward system coarse steps (xiPositiveTerminal system coarse),
      Finset.mem_image.mpr ⟨xiPositiveTerminal system coarse, Finset.mem_univ _, rfl⟩⟩
  have comparison := graphWalkChain_hitTime (XiSimpleGraph system (coarse + steps))
    (xiSimpleGraph_connected system rulesConnected (coarse + steps))
    (fun target => by
      exact_mod_cast xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) target)
    (Finset.univ.image (xiForward system coarse steps)) nonempty vertex
  change IGS.Sec31.hitTime (xiGraphWalkChain system rulesConnected (coarse + steps))
    (Finset.univ.image (xiForward system coarse steps)) vertex = _ at comparison
  rw [← comparison]
  unfold IGS.Sec31.hitTime
  exact ciSup_le fun time =>
    xiSkeleton_partialHit_le_replantedMaximum system rulesConnected rulesLoopless coarse steps time vertex

/-- The constant is uniform in both levels and every starting vertex.
Only the actual mass-resistance product occurs in the scale. -/
theorem xiSkeleton_expExit_spectral_upper (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ upper : ℝ, 0 < upper ∧ ∀ coarse steps (vertex : XiVtx system (coarse + steps)),
      expExit (XiSimpleGraph system (coarse + steps))
          (Finset.univ.image (xiForward system coarse steps))ᶜ vertex ≤
        upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps := by
  obtain ⟨upper, positive, bound⟩ := xiReplantedTerminalExitMaximum_spectral_upper system
    rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  exact ⟨upper, positive, fun coarse steps vertex =>
    (xiSkeleton_expExit_le_replantedMaximum system rulesConnected rulesLoopless coarse steps vertex).trans
      (bound steps)⟩

end
end EIGS

#print axioms EIGS.xiSkeleton_partialHit_le_replantedMaximum
#print axioms EIGS.xiSkeleton_expExit_le_replantedMaximum
#print axioms EIGS.xiSkeleton_expExit_spectral_upper
