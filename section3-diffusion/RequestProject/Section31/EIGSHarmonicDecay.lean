import RequestProject.Section31.EIGSHarmonicContraction

/-! Iterating the proved actual child-edge contraction gives geometric edge
oscillation decay for every constructed harmonic family. -/

namespace EIGS

variable {K : ℕ}

theorem xiHarmonicValues_edge_decay_of_step_contraction (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ)
    (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour =
        resistanceRate * resistanceVector colour)
    (contractionFactor : ℝ) (factorNonnegative : 0 ≤ contractionFactor)
    (stepContraction : ∀ level (oldValues : XiVtx system level → ℝ)
      (edge : XiEdge system.toRuleData (level + 1)),
      |xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair level oldValues (XiTail system (level + 1) edge) -
        xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair level oldValues (XiHead system (level + 1) edge)| ≤
        |oldValues (XiTail system level edge.1) - oldValues (XiHead system level edge.1)| * contractionFactor)
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ) (initialBound : ℝ)
    (initialEdgeBound : ∀ edge : XiEdge system.toRuleData initialLevel,
      |initialValues (XiTail system initialLevel edge) - initialValues (XiHead system initialLevel edge)| ≤ initialBound) :
    ∀ offset (edge : XiEdge system.toRuleData (initialLevel + offset)),
      |xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset
            (XiTail system (initialLevel + offset) edge) -
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset
            (XiHead system (initialLevel + offset) edge)| ≤
        contractionFactor ^ offset * initialBound := by
  intro offset
  induction offset with
  | zero =>
      intro edge
      simpa only [xiHarmonicValues, Nat.add_zero, pow_zero, one_mul] using initialEdgeBound edge
  | succ offset induction =>
      intro edge
      calc
        _ ≤ |xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset
                (XiTail system (initialLevel + offset) edge.1) -
            xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset
                (XiHead system (initialLevel + offset) edge.1)| * contractionFactor :=
          stepContraction (initialLevel + offset) _ edge
        _ ≤ (contractionFactor ^ offset * initialBound) * contractionFactor :=
          mul_le_mul_of_nonneg_right (induction edge.1) factorNonnegative
        _ = contractionFactor ^ (offset + 1) * initialBound := by rw [pow_succ]; ring

/-- Geometric edge decay with the factor and harmonic weights constructed from
the original standing graph assumptions, with no contraction hypothesis. -/
theorem exists_xiHarmonic_geometric_edge_decay (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour)) :
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ resistanceRatePositive : 0 < resistanceRate,
      ∃ resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour =
          resistanceRate * resistanceVector colour,
      ∃ contractionFactor : ℝ, 0 < contractionFactor ∧ contractionFactor < 1 ∧
        ∀ initialLevel (initialValues : XiVtx system initialLevel → ℝ) (initialBound : ℝ),
          (∀ edge : XiEdge system.toRuleData initialLevel,
            |initialValues (XiTail system initialLevel edge) - initialValues (XiHead system initialLevel edge)| ≤ initialBound) →
          ∀ offset (edge : XiEdge system.toRuleData (initialLevel + offset)),
            |xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
                resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset
                  (XiTail system (initialLevel + offset) edge) -
              xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
                resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset
                  (XiHead system (initialLevel + offset) edge)| ≤ contractionFactor ^ offset * initialBound := by
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, coordinateEigenpair,
      contractionFactor, factorPositive, factorStrict, stepContraction⟩ :=
    exists_xiHarmonic_strict_contraction system rulesConnected distancePositive oneColourDistance
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, coordinateEigenpair,
    contractionFactor, factorPositive, factorStrict, ?_⟩
  exact xiHarmonicValues_edge_decay_of_step_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive coordinateEigenpair contractionFactor factorPositive.le stepContraction

end EIGS
