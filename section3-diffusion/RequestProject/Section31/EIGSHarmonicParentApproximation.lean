import RequestProject.Section31.EIGSMetricCompactness
import RequestProject.Section31.EIGSHarmonicLinear
import RequestProject.Section31.EIGSHarmonicDecay
import RequestProject.Section31.EIGSCellConvexity

set_option maxHeartbeats 1200000

/-! The actual parent chain approximates a harmonic union function and the
actual path metric simultaneously. Both estimates use the very same coarse
vertex, which is needed for finite Lipschitz approximation. -/

namespace EIGS

variable {K : ℕ}

private theorem parentGeometricTailStep (ratio coarsePower finePower amplitude : ℝ)
    (denominatorNonzero : 1 - ratio ≠ 0) :
    finePower * amplitude + amplitude / (1 - ratio) * (coarsePower - finePower) =
      amplitude / (1 - ratio) * (coarsePower - finePower * ratio) := by
  field_simp [denominatorNonzero]
  ring

theorem xiHarmonicStep_parent_error (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (level : ℕ) (oldValues : XiVtx system level → ℝ) (edgeBound : ℝ) (boundNonnegative : 0 ≤ edgeBound)
    (edgeDifferenceBound : ∀ edge : XiEdge system.toRuleData level,
      |oldValues (XiTail system level edge) - oldValues (XiHead system level edge)| ≤ edgeBound)
    (vertex : XiVtx system (level + 1)) :
    |xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair level oldValues vertex -
      oldValues (xiParentVertex system level vertex)| ≤ edgeBound := by
  cases vertex with
  | inl oldVertex =>
      simpa only [xiParentVertex, xiHarmonicStep_old, sub_self, abs_zero] using boundNonnegative
  | inr privateVertex =>
      obtain ⟨edge, ruleVertex, notPlus, notMinus⟩ := privateVertex
      have embeddedPrivate : embedRuleVtx system level edge (XiTail system level edge)
          (XiHead system level edge) ruleVertex = Sum.inr ⟨edge, ⟨ruleVertex, notPlus, notMinus⟩⟩ := by
        simp [embedRuleVtx, notPlus, notMinus]
      have valueRange := xiHarmonicStep_rule_vertex_range system rulesConnected resistanceRate resistanceRatePositive
        resistanceVector resistanceVectorPositive renormalizationEigenpair level oldValues edge ruleVertex
      rw [embeddedPrivate] at valueRange
      change |xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair level oldValues (Sum.inr ⟨edge, ⟨ruleVertex, notPlus, notMinus⟩⟩) -
        oldValues (XiTail system level edge)| ≤ edgeBound
      have endpointBound := edgeDifferenceBound edge
      by_cases endpointOrder : oldValues (XiTail system level edge) ≤ oldValues (XiHead system level edge)
      · rw [min_eq_left endpointOrder, max_eq_right endpointOrder] at valueRange
        rw [abs_of_nonpos (sub_nonpos.2 endpointOrder)] at endpointBound
        exact abs_le.2 ⟨by linarith [valueRange.1], by linarith [valueRange.2]⟩
      · have reverseOrder : oldValues (XiHead system level edge) ≤ oldValues (XiTail system level edge) := le_of_not_ge endpointOrder
        rw [min_eq_right reverseOrder, max_eq_left reverseOrder] at valueRange
        rw [abs_of_nonneg (sub_nonneg.2 reverseOrder)] at endpointBound
        exact abs_le.2 ⟨by linarith [valueRange.1], by linarith [valueRange.2]⟩

section HarmonicApproximation

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (contractionFactor initialBound : ℝ) (factorPositive : 0 < contractionFactor)
    (factorStrict : contractionFactor < 1) (boundNonnegative : 0 ≤ initialBound)
    (edgeDecay : ∀ offset (edge : XiEdge system.toRuleData (initialLevel + offset)),
      |xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair initialLevel initialValues offset (XiTail system (initialLevel + offset) edge) -
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair initialLevel initialValues offset (XiHead system (initialLevel + offset) edge)| ≤
        contractionFactor ^ offset * initialBound)

include rulesConnected resistanceRatePositive resistanceVectorPositive renormalizationEigenpair
  factorPositive boundNonnegative edgeDecay

theorem xiHarmonicUnion_parent_error (offset : ℕ) (vertex : XiVtx system (initialLevel + offset + 1)) :
    |xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        renormalizationEigenpair initialLevel initialValues (xiVertexEmbedding system (initialLevel + offset + 1) vertex) -
      xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        renormalizationEigenpair initialLevel initialValues
          (xiVertexEmbedding system (initialLevel + offset) (xiParentVertex system (initialLevel + offset) vertex))| ≤
      contractionFactor ^ offset * initialBound := by
  have fineValues := xiHarmonicUnionExtension_values system rulesConnected resistanceRate resistanceRatePositive resistanceVector
    resistanceVectorPositive renormalizationEigenpair initialLevel initialValues (offset + 1) vertex
  change xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel initialValues
      (xiVertexEmbedding system (initialLevel + offset + 1) vertex) =
    xiHarmonicStep system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      renormalizationEigenpair (initialLevel + offset)
      (xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        renormalizationEigenpair initialLevel initialValues offset) vertex at fineValues
  rw [fineValues,
    xiHarmonicUnionExtension_values system rulesConnected resistanceRate resistanceRatePositive resistanceVector
    resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset]
  exact xiHarmonicStep_parent_error system rulesConnected resistanceRate resistanceRatePositive resistanceVector
    resistanceVectorPositive renormalizationEigenpair (initialLevel + offset) _
    (contractionFactor ^ offset * initialBound) (mul_nonneg (pow_pos factorPositive _).le boundNonnegative)
    (edgeDecay offset) vertex

include lengthsPositive distanceRateGreaterThanOne metricEigenpair factorStrict

theorem xiHarmonicFiniteLevel_joint_approximation (coarseOffset : ℕ) :
    ∀ fineOffset, coarseOffset ≤ fineOffset → ∀ vertex : XiVtx system (initialLevel + fineOffset),
      ∃ coarseVertex : XiVtx system (initialLevel + coarseOffset),
        xiUnionDistance system lengths distanceRate (xiVertexEmbedding system (initialLevel + fineOffset) vertex)
            (xiVertexEmbedding system (initialLevel + coarseOffset) coarseVertex) ≤
          xiRuleRadius system lengths / (1 - distanceRate⁻¹) *
            (distanceRate⁻¹ ^ (initialLevel + coarseOffset + 1) - distanceRate⁻¹ ^ (initialLevel + fineOffset + 1)) ∧
        |xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
            renormalizationEigenpair initialLevel initialValues (xiVertexEmbedding system (initialLevel + fineOffset) vertex) -
          xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
            renormalizationEigenpair initialLevel initialValues
              (xiVertexEmbedding system (initialLevel + coarseOffset) coarseVertex)| ≤
          initialBound / (1 - contractionFactor) * (contractionFactor ^ coarseOffset - contractionFactor ^ fineOffset) := by
  intro fineOffset levelsOrdered
  induction fineOffset, levelsOrdered using Nat.le_induction with
  | base =>
      intro vertex
      refine ⟨vertex, ?_, ?_⟩
      · rw [xiUnionDistance_self system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair]
        simp
      · simp
  | succ fineOffset levelsOrdered induction =>
      intro vertex
      obtain ⟨coarseVertex, distanceBound, valueBound⟩ := induction (xiParentVertex system (initialLevel + fineOffset) vertex)
      refine ⟨coarseVertex, ?_, ?_⟩
      · have triangle := xiUnionDistance_triangle system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair
          (xiVertexEmbedding system (initialLevel + fineOffset + 1) vertex)
          (xiVertexEmbedding system (initialLevel + fineOffset) (xiParentVertex system (initialLevel + fineOffset) vertex))
          (xiVertexEmbedding system (initialLevel + coarseOffset) coarseVertex)
        have parentBound := xiUnionDistance_parent_bound system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair (initialLevel + fineOffset) vertex
        have denominatorNonzero : 1 - distanceRate⁻¹ ≠ 0 :=
          ne_of_gt (sub_pos.mpr ((inv_lt_one₀ (zero_lt_one.trans distanceRateGreaterThanOne)).mpr distanceRateGreaterThanOne))
        have tailIdentity : distanceRate⁻¹ ^ (initialLevel + fineOffset + 1) * xiRuleRadius system lengths +
            xiRuleRadius system lengths / (1 - distanceRate⁻¹) *
              (distanceRate⁻¹ ^ (initialLevel + coarseOffset + 1) - distanceRate⁻¹ ^ (initialLevel + fineOffset + 1)) =
            xiRuleRadius system lengths / (1 - distanceRate⁻¹) *
              (distanceRate⁻¹ ^ (initialLevel + coarseOffset + 1) - distanceRate⁻¹ ^ (initialLevel + (fineOffset + 1) + 1)) := by
          rw [show initialLevel + (fineOffset + 1) + 1 = (initialLevel + fineOffset + 1) + 1 by omega, pow_succ]
          exact parentGeometricTailStep _ _ _ _ denominatorNonzero
        exact (triangle.trans (add_le_add parentBound distanceBound)).trans_eq tailIdentity
      · have triangle := abs_sub_le
          (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
            renormalizationEigenpair initialLevel initialValues (xiVertexEmbedding system (initialLevel + fineOffset + 1) vertex))
          (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
            renormalizationEigenpair initialLevel initialValues
              (xiVertexEmbedding system (initialLevel + fineOffset) (xiParentVertex system (initialLevel + fineOffset) vertex)))
          (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
            renormalizationEigenpair initialLevel initialValues
              (xiVertexEmbedding system (initialLevel + coarseOffset) coarseVertex))
        have parentBound := xiHarmonicUnion_parent_error system rulesConnected resistanceRate resistanceRatePositive
          resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel initialValues contractionFactor initialBound
          factorPositive boundNonnegative edgeDecay fineOffset vertex
        have tailIdentity : contractionFactor ^ fineOffset * initialBound + initialBound / (1 - contractionFactor) *
            (contractionFactor ^ coarseOffset - contractionFactor ^ fineOffset) =
            initialBound / (1 - contractionFactor) * (contractionFactor ^ coarseOffset - contractionFactor ^ (fineOffset + 1)) := by
          rw [pow_succ]
          exact parentGeometricTailStep _ _ _ _ (ne_of_gt (sub_pos.mpr factorStrict))
        exact (triangle.trans (add_le_add parentBound valueBound)).trans_eq tailIdentity

theorem xiHarmonicUnion_joint_approximation (coarseOffset : ℕ) (vertex : XiVertexUnion system) :
    ∃ coarseVertex : XiVtx system (initialLevel + coarseOffset),
      xiUnionDistance system lengths distanceRate vertex
          (xiVertexEmbedding system (initialLevel + coarseOffset) coarseVertex) ≤
        xiRuleRadius system lengths / (1 - distanceRate⁻¹) * distanceRate⁻¹ ^ (initialLevel + coarseOffset + 1) ∧
      |xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair initialLevel initialValues vertex -
        xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair initialLevel initialValues
            (xiVertexEmbedding system (initialLevel + coarseOffset) coarseVertex)| ≤
        initialBound / (1 - contractionFactor) * contractionFactor ^ coarseOffset := by
  let fineOffset := coarseOffset + xiUnionBirth system vertex
  have birthBound : xiUnionBirth system vertex ≤ initialLevel + fineOffset := by dsimp [fineOffset]; omega
  let finiteVertex := xiVertexAtLevel system vertex (initialLevel + fineOffset) birthBound
  obtain ⟨coarseVertex, distanceBound, valueBound⟩ := xiHarmonicFiniteLevel_joint_approximation
    system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
    resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
    initialLevel initialValues contractionFactor initialBound factorPositive factorStrict boundNonnegative edgeDecay
    coarseOffset fineOffset (by dsimp [fineOffset]; omega) finiteVertex
  have representsVertex : xiVertexEmbedding system (initialLevel + fineOffset) finiteVertex = vertex :=
    xiVertexEmbedding_atLevel system vertex (initialLevel + fineOffset) birthBound
  rw [representsVertex] at distanceBound valueBound
  refine ⟨coarseVertex, distanceBound.trans ?_, valueBound.trans ?_⟩
  · exact mul_le_mul_of_nonneg_left
      (sub_le_self _ (pow_nonneg (inv_pos.2 (zero_lt_one.trans distanceRateGreaterThanOne)).le _))
      (div_nonneg (xiRuleRadius_nonnegative system (fun colour => (lengthsPositive colour).le))
        (sub_pos.mpr ((inv_lt_one₀ (zero_lt_one.trans distanceRateGreaterThanOne)).mpr distanceRateGreaterThanOne)).le)
  · exact mul_le_mul_of_nonneg_left (sub_le_self _ (pow_pos factorPositive _).le)
      (div_nonneg boundNonnegative (sub_pos.mpr factorStrict).le)

end HarmonicApproximation

end EIGS
