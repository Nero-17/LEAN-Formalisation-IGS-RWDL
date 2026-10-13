import RequestProject.Section31.EIGSHarmonicCellL2Lower
import RequestProject.Section31.EIGSHarmonicL2Recovery

/-! The uniform reverse cell estimate for the constructed stationary harmonic
extension, and its passage to the actual limiting speed L² norm. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BigOperators BoundedContinuousFunction

variable {K : ℕ}

theorem xiHarmonicUnionRestriction_step (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (level : ℕ) (afterInitial : initialLevel ≤ level) :
    (fun vertex => xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair initialLevel initialValues (xiVertexEmbedding system (level + 1) vertex)) =
    xiHarmonicStep system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair level
      (fun vertex => xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        eigenpair initialLevel initialValues (xiVertexEmbedding system level vertex)) := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le afterInitial
  have oldAgreement :
      (fun vertex => xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        eigenpair initialLevel initialValues (xiVertexEmbedding system (initialLevel + offset) vertex)) =
      xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
        initialLevel initialValues offset := by
    funext vertex
    exact xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair initialLevel initialValues offset vertex
  rw [oldAgreement]
  funext vertex
  exact xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
    eigenpair initialLevel initialValues (offset + 1) vertex

theorem exists_xiHarmonic_native_reverse_bound (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour) :
    ∃ constant : ℝ, 0 < constant ∧ ∃ depth : ℕ, ∀ initialLevel
      (initialValues : XiVtx system initialLevel → ℝ) offset,
      constant / mass.rate ^ initialLevel *
        (∑ edge : XiEdge system.toRuleData initialLevel,
          ((initialValues (XiTail system initialLevel edge)) ^ 2 +
            (initialValues (XiHead system initialLevel edge)) ^ 2)) ≤
      ‖xiHarmonicNativeL2 system rulesConnected mass resistanceRate ratePositive resistanceVector vectorPositive
        eigenpair initialLevel initialValues (initialLevel + depth + offset)‖ ^ 2 := by
  obtain ⟨profiles, factor, factorPositive, factorStrict, profilesPlus, profilesMinus, profilesMinimal, profilesOscillation⟩ :=
    exists_rule_harmonic_profiles_strict_oscillation system rulesConnected distancePositive oneColourDistance resistanceVector vectorPositive
  have stepContraction := xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair profiles profilesPlus profilesMinus profilesMinimal factor profilesOscillation
  obtain ⟨constant, constantPositive, depth, lowerBound⟩ := exists_xiHarmonicFamily_native_lower system rulesConnected mass
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair factor factorPositive factorStrict stepContraction
  refine ⟨constant, constantPositive, depth, ?_⟩
  intro initialLevel initialValues offset
  have comparison := lowerBound initialLevel
    (fun level vertex => xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair initialLevel initialValues (xiVertexEmbedding system level vertex))
    (xiHarmonicUnionRestriction_step system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair initialLevel initialValues) offset
  have initialAgreement : ∀ vertex : XiVtx system initialLevel,
      xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        eigenpair initialLevel initialValues (xiVertexEmbedding system initialLevel vertex) = initialValues vertex :=
    xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair initialLevel initialValues 0
  simpa only [xiHarmonicNativeL2, if_pos (show initialLevel ≤ initialLevel + depth + offset by omega), initialAgreement] using comparison

theorem exists_xiContinuousHarmonic_reverse_L2_bound (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
    ∃ constant : ℝ, 0 < constant ∧ ∀ initialLevel (initialValues : XiVtx system initialLevel → ℝ)
      (extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
      (∀ offset (vertex : XiVtx system (initialLevel + offset)),
        extension (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair (initialLevel + offset) vertex) =
          xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
            initialLevel initialValues offset vertex) →
      constant / mass.rate ^ initialLevel *
        (∑ edge : XiEdge system.toRuleData initialLevel,
          ((initialValues (XiTail system initialLevel edge)) ^ 2 +
            (initialValues (XiHead system initialLevel edge)) ^ 2)) ≤
      ‖(xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass).embed
        (BoundedContinuousFunction.mkOfCompact extension)‖ ^ 2 := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
  obtain ⟨constant, constantPositive, depth, lowerBound⟩ := exists_xiHarmonic_native_reverse_bound system rulesConnected mass
    distancePositive oneColourDistance resistanceRate ratePositive resistanceVector vectorPositive eigenpair
  refine ⟨constant, constantPositive, ?_⟩
  intro initialLevel initialValues extension extensionValues
  have stateConvergence := xiHarmonicNativeL2_strong system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    initialLevel initialValues extension extensionValues
  have normConvergence := (xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass).strong_norm_tendsto stateConvergence
  apply ge_of_tendsto (normConvergence.pow 2)
  filter_upwards [eventually_ge_atTop (initialLevel + depth)] with level afterDepth
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le afterDepth
  exact lowerBound initialLevel initialValues offset

end EIGS
