import RequestProject.Section31.TraceDistinctDecomposition
import RequestProject.Section31.EIGSSkeletonTraceTransport
import RequestProject.Section31.EIGSReplantedSkeletonDuration
import RequestProject.Section31.EIGSReplantedRuleJumpTransport

/-! The actual replanted exit decomposition at the first-level skeleton.
Only its initial skeleton-reaching bound remains an input, to be supplied
by strict lower-depth cell localization. Jump and duration bounds are proved
for the actual kernels and filled internally. -/

namespace EIGS

open IGS.Sec31
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiForward_preserves_terminals (system : EIGSData K) (coarse steps : ℕ) :
    xiForward system coarse steps (xiPositiveTerminal system coarse) =
        xiPositiveTerminal system (coarse + steps) ∧
      xiForward system coarse steps (xiNegativeTerminal system coarse) =
        xiNegativeTerminal system (coarse + steps) := by
  induction steps with
  | zero => exact ⟨rfl, rfl⟩
  | succ steps induction =>
      constructor
      · change Sum.inl (xiForward system coarse steps (xiPositiveTerminal system coarse)) =
          Sum.inl (xiPositiveTerminal system (coarse + steps))
        exact congrArg Sum.inl induction.1
      · change Sum.inl (xiForward system coarse steps (xiNegativeTerminal system coarse)) =
          Sum.inl (xiNegativeTerminal system (coarse + steps))
        exact congrArg Sum.inl induction.2

theorem xiForward_terminals_image (system : EIGSData K) (coarse steps : ℕ) :
    ({xiPositiveTerminal system coarse, xiNegativeTerminal system coarse} :
      Finset (XiVtx system coarse)).image (xiForward system coarse steps) =
      {xiPositiveTerminal system (coarse + steps), xiNegativeTerminal system (coarse + steps)} := by
  simp only [Finset.image_insert, Finset.image_singleton,
    (xiForward_preserves_terminals system coarse steps).1,
    (xiForward_preserves_terminals system coarse steps).2]

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

theorem xiReplanted_exit_le_first_skeleton_add_spectral_cost :
    ∃ upper : ℝ, 0 < upper ∧ ∀ colour steps {reachBound : ℝ},
      (∀ time (vertex : XiVtx {system with initCol := colour} (1 + steps)),
        partialHit (xiGraphWalkChain {system with initCol := colour} rulesConnected (1 + steps))
          (Finset.univ.image (xiForward {system with initCol := colour} 1 steps)) time vertex ≤ reachBound) →
      ∀ vertex : XiVtx {system with initCol := colour} (1 + steps),
        hitTime (xiGraphWalkChain {system with initCol := colour} rulesConnected (1 + steps))
          {xiPositiveTerminal {system with initCol := colour} (1 + steps),
            xiNegativeTerminal {system with initCol := colour} (1 + steps)} vertex ≤
          reachBound + upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps ∧
        expExit (XiSimpleGraph {system with initCol := colour} (1 + steps))
          ({xiPositiveTerminal {system with initCol := colour} (1 + steps),
            xiNegativeTerminal {system with initCol := colour} (1 + steps)} :
              Finset (XiVtx {system with initCol := colour} (1 + steps)))ᶜ vertex ≤
          reachBound + upper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps := by
  obtain ⟨durationUpper, durationPositive, durationBound⟩ :=
    xiReplantedSkeletonDistinctDuration_spectral_upper system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive
  obtain ⟨jumpUpper, jumpPositive, jumpBound⟩ :=
    xiReplantedFirstSkeleton_uniform_terminal_jumps system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive
  have massPositive := (eigs_mass_spectral_growth system rulesConnected distancePositive).1
  have ratePositive := (system.resistanceSpectralRadius_positive_eigenpair
    rulesConnected distancePositive).1
  refine ⟨durationUpper * jumpUpper, mul_pos durationPositive jumpPositive, ?_⟩
  intro colour steps reachBound reach vertex
  have initialBound :
      hitTime (xiGraphWalkChain {system with initCol := colour} rulesConnected (1 + steps))
        {xiPositiveTerminal {system with initCol := colour} (1 + steps),
          xiNegativeTerminal {system with initCol := colour} (1 + steps)} vertex ≤
      reachBound + (durationUpper * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps) * jumpUpper := by
    apply exit_time_le_distinct_skeleton_add_cost
      (xiGraphWalkChain {system with initCol := colour} rulesConnected (1 + steps))
      (Finset.univ.image (xiForward {system with initCol := colour} 1 steps))
      {xiPositiveTerminal {system with initCol := colour} (1 + steps),
        xiNegativeTerminal {system with initCol := colour} (1 + steps)}
      (xiGraphWalk_hits_skeleton {system with initCol := colour} rulesConnected 1 steps) reach
      (xiSkeletonTrace_departure_positive {system with initCol := colour} rulesConnected
        1 steps rulesLoopless rulesUnique plantingNonadjacent)
      (mul_nonneg durationPositive.le (pow_nonneg (mul_nonneg massPositive.le ratePositive.le) steps))
      jumpPositive.le
    · intro target
      obtain ⟨source, rfl⟩ := (xiSkeletonVertexEquiv {system with initCol := colour} 1 steps).surjective target
      change excursionTime (xiGraphWalkChain {system with initCol := colour} rulesConnected (1 + steps))
          (Finset.univ.image (xiForward {system with initCol := colour} 1 steps))
          (xiSkeletonVertexEquiv {system with initCol := colour} 1 steps source) /
        (1 - (xiSkeletonTraceChain {system with initCol := colour} rulesConnected 1 steps).P
          (xiSkeletonVertexEquiv {system with initCol := colour} 1 steps source)
          (xiSkeletonVertexEquiv {system with initCol := colour} 1 steps source)) ≤ _
      rw [xiSkeletonTrace_duration, xiSkeletonTrace_transition]
      exact durationBound colour 1 steps source
    · intro time target
      obtain ⟨source, rfl⟩ := (xiSkeletonVertexEquiv {system with initCol := colour} 1 steps).surjective target
      have transported := xiSkeletonTrace_distinct_partialHit {system with initCol := colour}
        rulesConnected 1 steps rulesLoopless rulesUnique plantingNonadjacent
        {xiPositiveTerminal {system with initCol := colour} 1,
          xiNegativeTerminal {system with initCol := colour} 1} time source
      rw [xiForward_terminals_image] at transported
      change partialHit (xiSkeletonTraceDistinctChain {system with initCol := colour}
        rulesConnected 1 steps rulesLoopless rulesUnique plantingNonadjacent)
        (termIn (Finset.univ.image (xiForward {system with initCol := colour} 1 steps))
          {xiPositiveTerminal {system with initCol := colour} (1 + steps),
            xiNegativeTerminal {system with initCol := colour} (1 + steps)}) time
        (xiSkeletonVertexEquiv {system with initCol := colour} 1 steps source) ≤ _
      rw [transported]
      exact jumpBound colour steps time source
  have actualBound :
      hitTime (xiGraphWalkChain {system with initCol := colour} rulesConnected (1 + steps))
        {xiPositiveTerminal {system with initCol := colour} (1 + steps),
          xiNegativeTerminal {system with initCol := colour} (1 + steps)} vertex ≤
      reachBound + (durationUpper * jumpUpper) *
        (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps :=
    initialBound.trans_eq (by ring)
  refine ⟨actualBound, ?_⟩
  have meanEquality := graphWalkChain_hitTime
    (XiSimpleGraph {system with initCol := colour} (1 + steps))
    (xiSimpleGraph_connected {system with initCol := colour} rulesConnected (1 + steps))
    (fun target => by
      exact_mod_cast xiSimpleGraph_degree_positive {system with initCol := colour}
        rulesConnected (1 + steps) target)
    {xiPositiveTerminal {system with initCol := colour} (1 + steps),
      xiNegativeTerminal {system with initCol := colour} (1 + steps)}
    ⟨xiPositiveTerminal {system with initCol := colour} (1 + steps), by simp⟩ vertex
  change hitTime (xiGraphWalkChain {system with initCol := colour} rulesConnected (1 + steps))
      {xiPositiveTerminal {system with initCol := colour} (1 + steps),
        xiNegativeTerminal {system with initCol := colour} (1 + steps)} vertex = _ at meanEquality
  rw [← meanEquality]
  exact actualBound

end
end EIGS

#print axioms EIGS.xiForward_preserves_terminals
#print axioms EIGS.xiForward_terminals_image
#print axioms EIGS.xiReplanted_exit_le_first_skeleton_add_spectral_cost
