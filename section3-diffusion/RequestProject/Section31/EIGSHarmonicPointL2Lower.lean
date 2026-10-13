import RequestProject.Section31.EIGSHarmonicNativeLower

/-! Actual incidence-weighted point values are controlled by the uniform
reverse harmonic norm estimate. Counting both endpoint fibres remains exact. -/

namespace EIGS

open scoped BigOperators BoundedContinuousFunction

variable {K : ℕ}

theorem xiIncidence_square_le_endpoint_sum (system : EIGSData K)
    (level : ℕ) (values : XiVtx system level → ℝ) (vertex : XiVtx system level) :
    (xiVertexIncidenceCount system level vertex : ℝ) * (values vertex) ^ 2 ≤
      ∑ edge : XiEdge system.toRuleData level,
        ((values (XiTail system level edge)) ^ 2 + (values (XiHead system level edge)) ^ 2) := by
  classical
  have incidenceSum : (xiVertexIncidenceCount system level vertex : ℝ) =
      ∑ edge : XiEdge system.toRuleData level,
        ((if XiTail system level edge = vertex then (1 : ℝ) else 0) +
          (if XiHead system level edge = vertex then (1 : ℝ) else 0)) := by
    simp only [xiVertexIncidenceCount, Nat.cast_add, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, Finset.sum_add_distrib]
  rw [incidenceSum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro edge _
  by_cases tailEquality : XiTail system level edge = vertex <;>
    by_cases headEquality : XiHead system level edge = vertex <;>
    simp only [tailEquality, headEquality, ↓reduceIte, zero_add, add_zero, one_mul, zero_mul] <;>
    nlinarith [sq_nonneg (values (XiTail system level edge)), sq_nonneg (values (XiHead system level edge))]

theorem exists_xiContinuousHarmonic_point_L2_bound (system : EIGSData K)
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
      ∀ vertex : XiVtx system initialLevel,
      constant / mass.rate ^ initialLevel * (xiVertexIncidenceCount system initialLevel vertex : ℝ) *
        (initialValues vertex) ^ 2 ≤
      ‖(xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass).embed
        (BoundedContinuousFunction.mkOfCompact extension)‖ ^ 2 := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
  obtain ⟨constant, constantPositive, reverseBound⟩ := exists_xiContinuousHarmonic_reverse_L2_bound system rulesConnected
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass distancePositive oneColourDistance
    resistanceRate ratePositive resistanceVector vectorPositive eigenpair
  refine ⟨constant, constantPositive, ?_⟩
  intro initialLevel initialValues extension extensionValues vertex
  have comparison := mul_le_mul_of_nonneg_left (xiIncidence_square_le_endpoint_sum system initialLevel initialValues vertex)
    (div_pos constantPositive (pow_pos mass.rate_positive initialLevel)).le
  simpa only [mul_assoc] using comparison.trans (reverseBound initialLevel initialValues extension extensionValues)

end EIGS
