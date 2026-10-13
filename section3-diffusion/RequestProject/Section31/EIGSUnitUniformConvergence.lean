import RequestProject.Section31.EIGSUnitUniformEstimate

/-! Uniform convergence on all vertices of every original fine graph, obtained
from actual middle traces and actual descendant-cell range bounds. -/

namespace EIGS

open Filter Topology

set_option maxHeartbeats 1800000

variable {K : ℕ}

noncomputable def xiUnitPotentialUniformError (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (extension : XiVertexUnion system → ℝ) (level : ℕ) : ℝ :=
  if afterInitial : initialLevel ≤ level then
    ‖xiUnitPotentialAt system rulesConnected initialLevel level afterInitial initialValues -
      (fun vertex => extension (xiVertexEmbedding system level vertex))‖
  else 0

theorem xiUnitPotentialUniformError_tendsto_of_edge_decay (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (resistanceVector : Fin K → ℝ)
    (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector)))
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (extension : XiVertexUnion system → ℝ)
    (extensionValues : ∀ offset (vertex : XiVtx system (initialLevel + offset)),
      extension (xiVertexEmbedding system (initialLevel + offset) vertex) =
        xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair initialLevel initialValues offset vertex)
    (contractionFactor initialBound : ℝ) (factorNonnegative : 0 ≤ contractionFactor)
    (factorStrict : contractionFactor < 1) (boundNonnegative : 0 ≤ initialBound)
    (edgeDecay : ∀ offset (edge : XiEdge system.toRuleData (initialLevel + offset)),
      |xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair initialLevel initialValues offset (XiTail system (initialLevel + offset) edge) -
        xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair initialLevel initialValues offset (XiHead system (initialLevel + offset) edge)| ≤
        contractionFactor ^ offset * initialBound) :
    Tendsto (xiUnitPotentialUniformError system rulesConnected initialLevel initialValues extension) atTop (nhds 0) := by
  have geometricConvergence : Tendsto (fun offset : ℕ => 2 * (contractionFactor ^ offset * initialBound)) atTop (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one factorNonnegative factorStrict).mul_const initialBound).const_mul 2
  apply Metric.tendsto_atTop.2
  intro tolerance tolerancePositive
  obtain ⟨middleOffset, middleMesh⟩ := ((tendsto_order.1 geometricConvergence).2
    (tolerance / 2) (by linarith)).exists
  have middleConvergence := xiUnitPotentialAt_mesoscopic_harmonic_tendsto system rulesConnected resistanceRate
    normalization ratePositive normalizationPositive resistanceVector vectorPositive renormalizationEigenpair
    normalizedConvergence initialLevel middleOffset initialValues
  obtain ⟨threshold, middleClose⟩ := Metric.tendsto_atTop.1 middleConvergence (tolerance / 2) (by linarith)
  refine ⟨initialLevel + middleOffset + threshold, ?_⟩
  intro level afterThreshold
  have afterMiddle : initialLevel + middleOffset ≤ level := by omega
  obtain ⟨fineOffset, rfl⟩ := Nat.exists_eq_add_of_le afterMiddle
  have afterFineThreshold : threshold ≤ fineOffset := by omega
  have middleError := middleClose fineOffset afterFineThreshold
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at middleError
  have uniformBound := xiUnitPotentialAt_uniform_error_le system rulesConnected resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair initialLevel initialValues extension extensionValues middleOffset fineOffset
    (contractionFactor ^ middleOffset * initialBound) (edgeDecay middleOffset)
  have normBound : ‖xiUnitPotentialAt system rulesConnected initialLevel ((initialLevel + middleOffset) + fineOffset)
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)) initialValues -
      (fun vertex => extension (xiVertexEmbedding system ((initialLevel + middleOffset) + fineOffset) vertex))‖ ≤
    ‖(fun middleVertex : XiVtx system (initialLevel + middleOffset) =>
      xiUnitPotentialAt system rulesConnected initialLevel ((initialLevel + middleOffset) + fineOffset)
        ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)) initialValues
        (xiVertexInclusion system (initialLevel + middleOffset) ((initialLevel + middleOffset) + fineOffset)
          (Nat.le_add_right _ _) middleVertex)) -
      xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair initialLevel initialValues middleOffset‖ + 2 * (contractionFactor ^ middleOffset * initialBound) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro vertex
    exact uniformBound vertex
  rw [xiUnitPotentialUniformError, dif_pos ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)),
    Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact normBound.trans_lt (by linarith)

theorem exists_xiUnitPotential_uniform_harmonic_convergence (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour)) :
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate,
      ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∀ initialLevel (initialValues : XiVtx system initialLevel → ℝ),
        Tendsto (xiUnitPotentialUniformError system rulesConnected initialLevel initialValues
          (xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
            renormalizationEigenpair initialLevel initialValues)) atTop (nhds 0) := by
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceRate, normalization, resistanceVector, ratePositive, normalizationPositive,
      vectorPositive, normalized, eigenpair, normalizedConvergence⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_normalized_iterate_limit coloursPositive distancePositive
  have coordinateEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour :=
    fun colour => congrFun eigenpair colour
  obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
      profilesMinimal, profilesOscillation⟩ := exists_rule_harmonic_profiles_strict_oscillation system rulesConnected
    distancePositive oneColourDistance resistanceVector vectorPositive
  have stepContraction := xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive coordinateEigenpair profiles profilesPlus profilesMinus profilesMinimal
    contractionFactor profilesOscillation
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, coordinateEigenpair, ?_⟩
  intro initialLevel initialValues
  have initialEdgeBound : ∀ edge : XiEdge system.toRuleData initialLevel,
      |initialValues (XiTail system initialLevel edge) - initialValues (XiHead system initialLevel edge)| ≤ 2 * ‖initialValues‖ := by
    intro edge
    have firstBound := norm_le_pi_norm initialValues (XiTail system initialLevel edge)
    have secondBound := norm_le_pi_norm initialValues (XiHead system initialLevel edge)
    rw [Real.norm_eq_abs] at firstBound secondBound
    exact (abs_sub _ _).trans (by linarith)
  exact xiUnitPotentialUniformError_tendsto_of_edge_decay system rulesConnected resistanceRate normalization ratePositive
    normalizationPositive resistanceVector vectorPositive coordinateEigenpair normalizedConvergence initialLevel initialValues
    (xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      coordinateEigenpair initialLevel initialValues)
    (xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      coordinateEigenpair initialLevel initialValues) contractionFactor (2 * ‖initialValues‖) factorPositive.le factorStrict
    (by positivity) (xiHarmonicValues_edge_decay_of_step_contraction system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive coordinateEigenpair contractionFactor factorPositive.le stepContraction initialLevel
      initialValues (2 * ‖initialValues‖) initialEdgeBound)

end EIGS
