import RequestProject.Section31.EIGSHarmonicParentApproximation
import Mathlib.Topology.MetricSpace.Lipschitz

set_option maxHeartbeats 1600000

/-! Finite McShane extensions uniformly approximate the actual harmonic union
function. The increasing Lipschitz constants cancel the shrinking metric
parent tails; the remaining error decays at the proved harmonic edge rate. -/

namespace EIGS

variable {K : ℕ}

theorem exists_positive_colour_length_lower_bound (system : EIGSData K)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour) :
    ∃ minimumLength : ℝ, 0 < minimumLength ∧ ∀ colour, minimumLength ≤ lengths colour := by
  classical
  let selectedLengths := Finset.univ.image lengths
  have selectedNonempty : selectedLengths.Nonempty :=
    ⟨lengths system.initCol, Finset.mem_image.2 ⟨system.initCol, Finset.mem_univ _, rfl⟩⟩
  refine ⟨selectedLengths.min' selectedNonempty, ?_, ?_⟩
  · obtain ⟨colour, membership, equality⟩ := Finset.mem_image.1 (Finset.min'_mem selectedLengths selectedNonempty)
    rw [← equality]
    exact lengthsPositive colour
  · intro colour
    exact Finset.min'_le selectedLengths _ (Finset.mem_image.2 ⟨colour, Finset.mem_univ _, rfl⟩)

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
    (minimumLength : ℝ) (minimumLengthPositive : 0 < minimumLength)
    (lengthLowerBound : ∀ colour, minimumLength ≤ lengths colour)

include rulesConnected lengthsPositive distanceRateGreaterThanOne metricEigenpair resistanceRatePositive
  resistanceVectorPositive renormalizationEigenpair factorPositive factorStrict boundNonnegative edgeDecay
  minimumLengthPositive lengthLowerBound

theorem exists_xiHarmonic_lipschitz_approximation (coarseOffset : ℕ) :
    letI := xiUnionMetricSpace system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair
    ∃ approximation : XiVertexUnion system → ℝ,
      LipschitzWith ⟨contractionFactor ^ coarseOffset * initialBound / minimumLength *
        distanceRate ^ (initialLevel + coarseOffset), by positivity⟩ approximation ∧
      ∀ vertex,
        |xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
            renormalizationEigenpair initialLevel initialValues vertex - approximation vertex| ≤
          contractionFactor ^ coarseOffset *
            (initialBound / (1 - contractionFactor) + initialBound / minimumLength *
              (xiRuleRadius system lengths / (1 - distanceRate⁻¹)) * distanceRate⁻¹) := by
  letI := xiUnionMetricSpace system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair
  have ratePositive : 0 < distanceRate := zero_lt_one.trans distanceRateGreaterThanOne
  have harmonicLipschitz : LipschitzOnWith
      ⟨contractionFactor ^ coarseOffset * initialBound / minimumLength * distanceRate ^ (initialLevel + coarseOffset), by positivity⟩
      (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        renormalizationEigenpair initialLevel initialValues) (xiLevelVertices system (initialLevel + coarseOffset)) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨source, rfl⟩ _ ⟨sink, rfl⟩
    have edgeLipschitz : (XiNetwork system (initialLevel + coarseOffset)).EdgeLipschitz
        ((contractionFactor ^ coarseOffset * initialBound / minimumLength) • lengths)
        (xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair initialLevel initialValues coarseOffset) := by
      intro edge
      change _ ≤ (contractionFactor ^ coarseOffset * initialBound / minimumLength) *
        lengths (XiCol system.toRuleData (initialLevel + coarseOffset) edge)
      calc
        _ ≤ contractionFactor ^ coarseOffset * initialBound := edgeDecay coarseOffset edge
        _ = (contractionFactor ^ coarseOffset * initialBound / minimumLength) * minimumLength :=
          (div_mul_cancel₀ _ minimumLengthPositive.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (lengthLowerBound _) (by positivity)
    have potentialBound := (XiNetwork system (initialLevel + coarseOffset)).potential_difference_le_weightedDistance
      (xiSimpleGraph_connected system rulesConnected _) edgeLipschitz source sink
    rw [Network.weightedDistance_smul _ _ (by positivity)] at potentialBound
    change |xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair initialLevel initialValues (xiVertexEmbedding system (initialLevel + coarseOffset) source) -
        xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair initialLevel initialValues (xiVertexEmbedding system (initialLevel + coarseOffset) sink)| ≤
      (contractionFactor ^ coarseOffset * initialBound / minimumLength * distanceRate ^ (initialLevel + coarseOffset)) *
        xiUnionDistance system lengths distanceRate (xiVertexEmbedding system (initialLevel + coarseOffset) source)
          (xiVertexEmbedding system (initialLevel + coarseOffset) sink)
    rw [xiHarmonicUnionExtension_values system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel initialValues coarseOffset source,
      xiHarmonicUnionExtension_values system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel initialValues coarseOffset sink,
      xiUnionDistance_embedding system rulesConnected lengths lengthsPositive distanceRate ratePositive metricEigenpair]
    have cancellation : distanceRate ^ (initialLevel + coarseOffset) * distanceRate⁻¹ ^ (initialLevel + coarseOffset) = 1 := by
      rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ ratePositive.ne')]
    change _ ≤ (contractionFactor ^ coarseOffset * initialBound / minimumLength * distanceRate ^ (initialLevel + coarseOffset)) *
      (distanceRate⁻¹ ^ (initialLevel + coarseOffset) * _)
    have productEquality :
        (contractionFactor ^ coarseOffset * initialBound / minimumLength * distanceRate ^ (initialLevel + coarseOffset)) *
          (distanceRate⁻¹ ^ (initialLevel + coarseOffset) *
            (XiNetwork system (initialLevel + coarseOffset)).weightedDistance lengths source sink) =
        (contractionFactor ^ coarseOffset * initialBound / minimumLength) *
          (XiNetwork system (initialLevel + coarseOffset)).weightedDistance lengths source sink := by
      calc
        _ = (contractionFactor ^ coarseOffset * initialBound / minimumLength) *
            (distanceRate ^ (initialLevel + coarseOffset) * distanceRate⁻¹ ^ (initialLevel + coarseOffset)) *
            (XiNetwork system (initialLevel + coarseOffset)).weightedDistance lengths source sink := by ring
        _ = _ := by rw [cancellation]; ring
    rw [productEquality]
    exact potentialBound
  obtain ⟨approximation, approximationLipschitz, finiteAgreement⟩ := harmonicLipschitz.extend_real
  refine ⟨approximation, approximationLipschitz, ?_⟩
  intro vertex
  obtain ⟨coarseVertex, distanceBound, valueBound⟩ := xiHarmonicUnion_joint_approximation
    system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
    resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
    initialLevel initialValues contractionFactor initialBound factorPositive factorStrict boundNonnegative edgeDecay
    coarseOffset vertex
  have coarseAgreement : approximation (xiVertexEmbedding system (initialLevel + coarseOffset) coarseVertex) =
      xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        renormalizationEigenpair initialLevel initialValues (xiVertexEmbedding system (initialLevel + coarseOffset) coarseVertex) :=
    (finiteAgreement ⟨coarseVertex, rfl⟩).symm
  change dist vertex (xiVertexEmbedding system (initialLevel + coarseOffset) coarseVertex) ≤ _ at distanceBound
  have approximationBound := approximationLipschitz.dist_le_mul_of_le distanceBound
  rw [Real.dist_eq, coarseAgreement] at approximationBound
  have cancellation : distanceRate ^ (initialLevel + coarseOffset) * distanceRate⁻¹ ^ (initialLevel + coarseOffset + 1) = distanceRate⁻¹ := by
    rw [pow_succ, inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ratePositive.ne'), one_mul]
  have productIdentity :
      (contractionFactor ^ coarseOffset * initialBound / minimumLength * distanceRate ^ (initialLevel + coarseOffset)) *
        (xiRuleRadius system lengths / (1 - distanceRate⁻¹) * distanceRate⁻¹ ^ (initialLevel + coarseOffset + 1)) =
      contractionFactor ^ coarseOffset * (initialBound / minimumLength *
        (xiRuleRadius system lengths / (1 - distanceRate⁻¹)) * distanceRate⁻¹) := by
    calc
      _ = (contractionFactor ^ coarseOffset * initialBound / minimumLength *
          (xiRuleRadius system lengths / (1 - distanceRate⁻¹))) *
          (distanceRate ^ (initialLevel + coarseOffset) * distanceRate⁻¹ ^ (initialLevel + coarseOffset + 1)) := by ring
      _ = _ := by rw [cancellation]; ring
  change |approximation vertex - _| ≤
    (contractionFactor ^ coarseOffset * initialBound / minimumLength * distanceRate ^ (initialLevel + coarseOffset)) * _
    at approximationBound
  rw [productIdentity] at approximationBound
  have triangle := abs_sub_le
    (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      renormalizationEigenpair initialLevel initialValues vertex)
    (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      renormalizationEigenpair initialLevel initialValues (xiVertexEmbedding system (initialLevel + coarseOffset) coarseVertex))
    (approximation vertex)
  rw [abs_sub_comm (approximation vertex)
    (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      renormalizationEigenpair initialLevel initialValues (xiVertexEmbedding system (initialLevel + coarseOffset) coarseVertex))]
    at approximationBound
  calc
    _ ≤ initialBound / (1 - contractionFactor) * contractionFactor ^ coarseOffset +
        contractionFactor ^ coarseOffset * (initialBound / minimumLength *
          (xiRuleRadius system lengths / (1 - distanceRate⁻¹)) * distanceRate⁻¹) :=
      triangle.trans (add_le_add valueBound approximationBound)
    _ = _ := by ring

end HarmonicApproximation

end EIGS
