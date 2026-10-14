import RequestProject.Section31.EIGSFiniteHorizonStepPathLawOfRules
import RequestProject.Section2ConcreteSimplicity

/-! Exact same-witness identification of the actual native walk clock with
paper a_n = 2 c_Psi rho(Psi)^n |E(Xi^n)|. The edge factor is the edgeFinset
cardinality of the actual underlying simple graph. The positive eigenvalue
is identified with the canonical nonlinear spectral radius internally.

Reference: paper-corrections/AIM.corrected.tex:2783-2793, fixed SHA256
06783166c1b05e8340edd98956319445b5a55056b47c2c9c60b65ce782746792.
The normalization in each equality is the very same witness on both sides.
No equality between independently rescaled eigenvectors is presumed. -/

namespace EIGS
noncomputable section
open Filter Topology
open scoped BigOperators NNReal
variable {K : ℕ}

def xiPaperFiniteWalkClock (system : EIGSData K) (level : ℕ)
    (resistanceRate normalization : ℝ) : ℝ :=
  2 * normalization * resistanceRate ^ level * ((XiSimpleGraph system level).edgeFinset.card : ℝ)

theorem xiTotalEdges_eq_actualSimpleGraphEdgeCard (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour)) (level : ℕ) :
    totalEdges system.toRuleData level = (XiSimpleGraph system level).edgeFinset.card := by
  classical
  change Fintype.card (XiNetwork system level).E = _
  have edgeCard := xiNetwork_card_edges_eq_simpleGraph system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level
  refine edgeCard.trans ?_
  exact congrArg
    (fun finite : Fintype (XiSimpleGraph system level).edgeSet =>
      (@SimpleGraph.edgeFinset _ (XiSimpleGraph system level) finite).card)
    (Subsingleton.elim _ _)

theorem xiNativeFiniteJumpRateNNReal_eq_paperClock (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization) (level : ℕ) :
    (xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive level : ℝ) =
      xiPaperFiniteWalkClock system level resistanceRate normalization := by
  have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
    ratePositive vectorPositive (by funext colour; exact renormalizationEigenpair colour)
  change xiNativeFiniteJumpRate system level (system.resistanceSpectralRadius rulesConnected distancePositive) normalization = _
  rw [← rateEquality]
  unfold xiNativeFiniteJumpRate xiPaperFiniteWalkClock
  rw [xiTotalEdges_eq_actualSimpleGraphEdgeCard system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level]

theorem xiNative_floor_index_eq_paperClock (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization) (level : ℕ) (time : ℝ) :
    ⌊time * (xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive level : ℝ)⌋₊ =
      ⌊time * xiPaperFiniteWalkClock system level resistanceRate normalization⌋₊ := by
  rw [xiNativeFiniteJumpRateNNReal_eq_paperClock system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive level]

theorem exists_xiPaperNativeClock_of_positive_eigenpair (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) :
    ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun level => fun colour => (system.ruleFamily rulesConnected).Psi^[level] (fun _ => 1) colour /
        resistanceRate ^ level) atTop (𝓝 (normalization • resistanceVector)) ∧
      (∀ level, (xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive
        normalization normalizationPositive level : ℝ) = xiPaperFiniteWalkClock system level resistanceRate normalization) ∧
      ∀ level (time : ℝ),
        ⌊time * (xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive level : ℝ)⌋₊ =
          ⌊time * xiPaperFiniteWalkClock system level resistanceRate normalization⌋₊ := by
  obtain ⟨normalization, normalizationPositive, convergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  exact ⟨normalization, normalizationPositive, convergence,
    xiNativeFiniteJumpRateNNReal_eq_paperClock system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive,
    xiNative_floor_index_eq_paperClock system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive⟩

end
end EIGS

#print axioms EIGS.xiTotalEdges_eq_actualSimpleGraphEdgeCard
#print axioms EIGS.xiNativeFiniteJumpRateNNReal_eq_paperClock
#print axioms EIGS.xiNative_floor_index_eq_paperClock
#print axioms EIGS.exists_xiPaperNativeClock_of_positive_eigenpair
