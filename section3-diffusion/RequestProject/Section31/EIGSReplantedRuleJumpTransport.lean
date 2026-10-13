import RequestProject.Section31.NetworkCellEmbeddingSurjectivity
import RequestProject.Section31.NetworkConductanceEmbeddingTransport
import RequestProject.Section31.XiNetworkIteratedSubstitution
import RequestProject.Section31.EIGSRuleConductanceJumpBound
import RequestProject.Section31.EIGSSkeletonConductance
import RequestProject.Section31.KilledChainEmbeddingTransport

/-! The entire first coarse graph of a replanted system is its actual rule.
Actual oriented edges, their colours and both terminals are transported.
The resulting distinct return chain inherits the proved fixed-rule jump
bound without a presumed kernel identity or an ambient-parent bound. -/

namespace EIGS

open IGS.Sec31
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (colour : Fin K)

private theorem initialEdgeLoopless : (Network.singleEdge colour).Loopless := by
  intro edge
  change (false : Bool) ≠ true
  decide

/-- Literal carrier injections avoid transporting finite instances through
an equality of whole network records. Both endpoint identities are actual. -/
def xiReplantedFirstRuleEmbedding : Network.ColourEmbedding (system.ruleNetwork colour)
    (XiNetwork {system with initCol := colour} 1) where
  vertex := ((Network.singleEdge colour).firstCopyEmbedding (system.ruleFamily rulesConnected)
    (initialEdgeLoopless colour) ()).vertex
  edge := ((Network.singleEdge colour).firstCopyEmbedding (system.ruleFamily rulesConnected)
    (initialEdgeLoopless colour) ()).edge
  tail _ := rfl
  head _ := rfl
  colour _ := rfl

theorem xiReplantedFirstRule_surjective :
    Function.Surjective (xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex ∧
      Function.Surjective (xiReplantedFirstRuleEmbedding system rulesConnected colour).edge :=
  ⟨Network.firstCopy_singleEdge_vertex_surjective (system.ruleFamily rulesConnected) colour
      (initialEdgeLoopless colour),
    Network.firstCopy_singleEdge_edge_surjective (system.ruleFamily rulesConnected) colour
      (initialEdgeLoopless colour)⟩

def xiReplantedFirstRuleEquiv :
    (system.ruleNetwork colour).V ≃ XiVtx {system with initCol := colour} 1 :=
  Equiv.ofBijective (xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex
    ⟨(xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex.injective,
      (xiReplantedFirstRule_surjective system rulesConnected colour).1⟩

theorem xiReplantedFirstRule_terminals :
    (xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex (system.plantPlus colour) =
        xiPositiveTerminal {system with initCol := colour} 1 ∧
      (xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex (system.plantMinus colour) =
        xiNegativeTerminal {system with initCol := colour} 1 := by
  constructor
  · change (Network.singleEdge colour).substEmbed (system.ruleFamily rulesConnected) ()
      ((system.ruleFamily rulesConnected).βplus colour) = Sum.inl false
    simp [Network.substEmbed, Network.singleEdge]
  · change (Network.singleEdge colour).substEmbed (system.ruleFamily rulesConnected) ()
      ((system.ruleFamily rulesConnected).βminus colour) = Sum.inl true
    simp [Network.substEmbed, Network.singleEdge, ((system.ruleFamily rulesConnected).plant_ne colour).symm]

theorem xiReplantedFirstRule_boundary_iff (source : (system.ruleNetwork colour).V) :
    (xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex source ∈
      ({xiPositiveTerminal {system with initCol := colour} 1,
        xiNegativeTerminal {system with initCol := colour} 1} :
          Finset (XiVtx {system with initCol := colour} 1)) ↔
    source ∈ ({system.plantPlus colour, system.plantMinus colour} :
      Finset (system.ruleNetwork colour).V) := by
  rw [← (xiReplantedFirstRule_terminals system rulesConnected colour).1,
    ← (xiReplantedFirstRule_terminals system rulesConnected colour).2]
  simp only [Finset.mem_insert, Finset.mem_singleton,
    (xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex.injective.eq_iff]

theorem xiReplantedFirstRule_conductance (steps : ℕ)
    (source target : (system.ruleNetwork colour).V) :
    xiSkeletonConductance {system with initCol := colour} rulesConnected 1 steps
      ((xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex source)
      ((xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex target) =
      xiRuleEffectiveConductance system rulesConnected colour steps source target := by
  change (XiNetwork {system with initCol := colour} 1).colourConductance
      (fun edgeColour => (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1)) edgeColour)⁻¹)
      ((xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex source)
      ((xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex target) =
    (system.ruleNetwork colour).colourConductance
      (fun edgeColour => (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1)) edgeColour)⁻¹)
      source target
  apply (xiReplantedFirstRuleEmbedding system rulesConnected colour).colourConductance_map
  intro edge _
  exact (xiReplantedFirstRule_surjective system rulesConnected colour).2 edge

theorem xiReplantedFirstRule_conductance_rowMass (steps : ℕ)
    (source : (system.ruleNetwork colour).V) :
    (∑ target : XiVtx {system with initCol := colour} 1,
      xiSkeletonConductance {system with initCol := colour} rulesConnected 1 steps
        ((xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex source) target) =
    ∑ target, xiRuleEffectiveConductance system rulesConnected colour steps source target := by
  change (∑ target : (XiNetwork {system with initCol := colour} 1).V,
      (XiNetwork {system with initCol := colour} 1).colourConductance
        (fun edgeColour => (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1)) edgeColour)⁻¹)
        ((xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex source) target) =
    ∑ target : (system.ruleNetwork colour).V,
      (system.ruleNetwork colour).colourConductance
        (fun edgeColour => (((system.ruleFamily rulesConnected).Psi^[steps] (fun _ => 1)) edgeColour)⁻¹)
        source target
  apply (xiReplantedFirstRuleEmbedding system rulesConnected colour).colourConductance_rowMass
  intro edge _
  exact (xiReplantedFirstRule_surjective system rulesConnected colour).2 edge

variable (rulesLoopless : ∀ ruleColour, (system.ruleNetwork ruleColour).Loopless)
    (rulesUnique : ∀ ruleColour, (system.ruleNetwork ruleColour).EdgesUnique)
    (plantingNonadjacent : ∀ ruleColour, ¬ (ruleSG system ruleColour).Adj
      (system.plantPlus ruleColour) (system.plantMinus ruleColour))

theorem xiReplantedFirstRule_distinct_transition (steps : ℕ)
    (source target : (system.ruleNetwork colour).V) :
    (distinctJumpChain (xiSkeletonReturnChain {system with initCol := colour} rulesConnected 1 steps)
      (xiSkeletonReturnChain_departure_positive {system with initCol := colour} rulesConnected
        rulesLoopless rulesUnique plantingNonadjacent 1 steps)).P
      ((xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex source)
      ((xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex target) =
    (xiRuleConductanceChain system rulesConnected colour steps).P source target := by
  rw [xiSkeleton_distinctJumpChain_eq_conductance {system with initCol := colour} rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent 1 steps]
  change xiSkeletonConductance {system with initCol := colour} rulesConnected 1 steps
      ((xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex source)
      ((xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex target) /
      (∑ other, xiSkeletonConductance {system with initCol := colour} rulesConnected 1 steps
        ((xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex source) other) =
    xiRuleEffectiveConductance system rulesConnected colour steps source target /
      ∑ other, xiRuleEffectiveConductance system rulesConnected colour steps source other
  rw [xiReplantedFirstRule_conductance, xiReplantedFirstRule_conductance_rowMass]

theorem xiReplantedFirstRule_distinct_partialHit (steps time : ℕ)
    (source : (system.ruleNetwork colour).V) :
    partialHit
      (distinctJumpChain (xiSkeletonReturnChain {system with initCol := colour} rulesConnected 1 steps)
        (xiSkeletonReturnChain_departure_positive {system with initCol := colour} rulesConnected
          rulesLoopless rulesUnique plantingNonadjacent 1 steps))
      {xiPositiveTerminal {system with initCol := colour} 1,
        xiNegativeTerminal {system with initCol := colour} 1} time
      ((xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex source) =
    partialHit (xiRuleConductanceChain system rulesConnected colour steps)
      {system.plantPlus colour, system.plantMinus colour} time source := by
  apply killedEmbedding_partialHit (xiRuleConductanceChain system rulesConnected colour steps)
    (distinctJumpChain (xiSkeletonReturnChain {system with initCol := colour} rulesConnected 1 steps)
      (xiSkeletonReturnChain_departure_positive {system with initCol := colour} rulesConnected
        rulesLoopless rulesUnique plantingNonadjacent 1 steps))
    (xiReplantedFirstRuleEmbedding system rulesConnected colour).vertex _ _
    (xiReplantedFirstRule_boundary_iff system rulesConnected colour)
    (fun first _ second => xiReplantedFirstRule_distinct_transition system rulesConnected colour
      rulesLoopless rulesUnique plantingNonadjacent steps first second)
    (fun _ _ target outside => False.elim
      (outside ((xiReplantedFirstRule_surjective system rulesConnected colour).1 target)))

variable (distancePositive : ∀ ruleColour edgeColour : Fin K,
    ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
      (system.plantPlus ruleColour) (system.plantMinus ruleColour))

include distancePositive

theorem xiReplantedFirstSkeleton_uniform_terminal_jumps :
    ∃ jumpBound : ℝ, 0 < jumpBound ∧ ∀ colour steps time
      (source : XiVtx {system with initCol := colour} 1),
      partialHit
        (distinctJumpChain (xiSkeletonReturnChain {system with initCol := colour} rulesConnected 1 steps)
          (xiSkeletonReturnChain_departure_positive {system with initCol := colour} rulesConnected
            rulesLoopless rulesUnique plantingNonadjacent 1 steps))
        {xiPositiveTerminal {system with initCol := colour} 1,
          xiNegativeTerminal {system with initCol := colour} 1} time source ≤ jumpBound := by
  obtain ⟨jumpBound, jumpBoundPositive, bound⟩ :=
    xiRuleConductanceChain_uniform_terminal_jumps system rulesConnected distancePositive
  refine ⟨jumpBound, jumpBoundPositive, ?_⟩
  intro ruleColour steps time source
  obtain ⟨original, rfl⟩ := (xiReplantedFirstRule_surjective system rulesConnected ruleColour).1 source
  rw [xiReplantedFirstRule_distinct_partialHit system rulesConnected ruleColour rulesLoopless
    rulesUnique plantingNonadjacent]
  exact bound ruleColour steps time original

end
end EIGS

#print axioms EIGS.xiReplantedFirstRuleEmbedding
#print axioms EIGS.xiReplantedFirstRule_surjective
#print axioms EIGS.xiReplantedFirstRuleEquiv
#print axioms EIGS.xiReplantedFirstRule_terminals
#print axioms EIGS.xiReplantedFirstRule_boundary_iff
#print axioms EIGS.xiReplantedFirstRule_conductance
#print axioms EIGS.xiReplantedFirstRule_conductance_rowMass
#print axioms EIGS.xiReplantedFirstRule_distinct_transition
#print axioms EIGS.xiReplantedFirstRule_distinct_partialHit
#print axioms EIGS.xiReplantedFirstSkeleton_uniform_terminal_jumps
