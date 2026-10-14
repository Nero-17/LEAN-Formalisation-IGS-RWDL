import RequestProject.Section31.EIGSOriginalCommonPathTransportOfRules
import RequestProject.Section31.EIGSPaperNativeClock

/-! Add the exact paper clock to the very same eigenpair, normalization,
closed semigroup, global continuous family and common ambient path witness.
The normalization is inherited from the actual path construction rather
than chosen a second time. All conclusions below remain on finite horizons;
no whole-time local-J1 or Polish conclusion is asserted. -/

namespace EIGS
noncomputable section
open Filter Topology
open scoped NNReal
variable {K : ℕ}

theorem exists_xiIdentifiedOriginalCommonPathPaperClock_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
        Tendsto (fun level => fun colour =>
          (system.ruleFamily rulesConnected).Psi^[level] (fun _ => 1) colour / resistanceRate ^ level)
          atTop (𝓝 (normalization • resistanceVector)) ∧
        XiIdentifiedOriginalCommonPathTransportProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
          normalization normalizationPositive ∧
        (∀ level, (xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive level : ℝ) =
          xiPaperFiniteWalkClock system level resistanceRate normalization) ∧
        ∀ level (time : ℝ),
          ⌊time * (xiNativeFiniteJumpRateNNReal system rulesConnected distancePositive normalization normalizationPositive level : ℝ)⌋₊ =
            ⌊time * xiPaperFiniteWalkClock system level resistanceRate normalization⌋₊ := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, pathProperties⟩ :=
    exists_xiIdentifiedOriginalCommonPathTransport_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, pathProperties,
    xiNativeFiniteJumpRateNNReal_eq_paperClock system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive,
    xiNative_floor_index_eq_paperClock system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive⟩

end
end EIGS

#print axioms EIGS.exists_xiIdentifiedOriginalCommonPathPaperClock_of_rules
