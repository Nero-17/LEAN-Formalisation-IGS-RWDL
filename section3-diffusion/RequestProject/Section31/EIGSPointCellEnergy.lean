import RequestProject.Section31.EIGSFiniteEnergyGeometricTail
import RequestProject.Section31.EIGSPhysicalClosedCell
import RequestProject.Section31.EIGSAddressHarmonicCellEnergy

/-! Uniform point-to-terminal energy control on actual physical closed cells.
The geometric projection estimate and the actual finite edge energy supply
the bound for every continuous finite-energy function, including cell limits.
This source is a candidate until its whole-file compilation is accepted. -/

namespace EIGS
open IGS.Sec31
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem xiUnion_edge_square_energy_bound (system : EIGSData K)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (values : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive)
    (level : ℕ) (edge : XiEdge system.toRuleData level) :
    (values.val (xiVertexEmbedding system level (XiTail system level edge)) -
      values.val (xiVertexEmbedding system level (XiHead system level edge))) ^ 2 ≤
      (∑ colour, resistanceVector colour) / resistanceRate ^ level *
        (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive values.val).toReal := by
  have finiteBound := finite_energy_le_traceEnergyValue
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive) values level
  rw [xiUnionWeightedNetwork_energy_eq] at finiteBound
  have singleBound := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun other : XiEdge system.toRuleData level =>
      (resistanceRate ^ level * (resistanceVector (XiCol system.toRuleData level other))⁻¹) *
        (values.val (xiVertexEmbedding system level (XiTail system level other)) -
          values.val (xiVertexEmbedding system level (XiHead system level other))) ^ 2)
    (fun other _ => mul_nonneg (mul_pos (pow_pos ratePositive _)
      (inv_pos.mpr (vectorPositive _))).le (sq_nonneg _)) (Finset.mem_univ edge)
  have scaled := mul_le_mul_of_nonneg_left (singleBound.trans finiteBound)
    (div_pos (vectorPositive (XiCol system.toRuleData level edge)) (pow_pos ratePositive level)).le
  have cancellation : resistanceVector (XiCol system.toRuleData level edge) / resistanceRate ^ level *
      ((resistanceRate ^ level * (resistanceVector (XiCol system.toRuleData level edge))⁻¹) *
        (values.val (xiVertexEmbedding system level (XiTail system level edge)) -
          values.val (xiVertexEmbedding system level (XiHead system level edge))) ^ 2) =
      (values.val (xiVertexEmbedding system level (XiTail system level edge)) -
        values.val (xiVertexEmbedding system level (XiHead system level edge))) ^ 2 := by
    field_simp [ne_of_gt ratePositive, ne_of_gt (vectorPositive _)]
  rw [cancellation] at scaled
  exact scaled.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right
      (Finset.single_le_sum (fun colour _ => (vectorPositive colour).le)
        (Finset.mem_univ (XiCol system.toRuleData level edge))) (pow_pos ratePositive level).le)
    ENNReal.toReal_nonneg)

section Completion
variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (rateGreaterThanOne : 1 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)

local instance : CompactSpace (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :=
  xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair

include eigenpair in
theorem exists_xiPhysicalClosedCell_point_terminal_energy_bound
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour)) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ target : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair resistanceRate (zero_lt_one.trans rateGreaterThanOne)
          resistanceVector vectorPositive,
      ∀ level (edge : XiEdge system.toRuleData level) point,
        point ∈ xiPhysicalClosedCell system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair level edge →
      ∀ terminal : XiVtx system level,
        (terminal = XiTail system level edge ∨ terminal = XiHead system level edge) →
        (target.val point - target.val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive
          distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level terminal)) ^ 2 ≤
        constant / resistanceRate ^ level *
          (xiExtendedWeightedEnergy system resistanceRate (zero_lt_one.trans rateGreaterThanOne)
            resistanceVector vectorPositive (target.val ∘ xiCompletionUnionEmbedding system rulesConnected
              lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
      profilesMinimal, profilesOscillation⟩ := exists_rule_harmonic_profiles_strict_oscillation system rulesConnected
    distancePositive oneColourDistance resistanceVector vectorPositive
  have stepContraction := xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate
    (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive eigenpair profiles profilesPlus profilesMinus
    profilesMinimal contractionFactor profilesOscillation
  obtain ⟨tailConstant, tailPositive, tailBound⟩ :=
    exists_xiContinuousHarmonicProjection_geometric_energy_tail system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate rateGreaterThanOne resistanceVector
      vectorPositive eigenpair contractionFactor factorPositive factorStrict stepContraction
  have vectorUpperPositive : 0 < ∑ colour, resistanceVector colour :=
    (vectorPositive system.initCol).trans_le (Finset.single_le_sum
      (fun colour _ => (vectorPositive colour).le) (Finset.mem_univ system.initCol))
  refine ⟨2 * (tailConstant ^ 2 + ∑ colour, resistanceVector colour), by positivity, ?_⟩
  intro target level edge point pointMembership terminal terminalMembership
  choose approximation approximationAgreement using fun boundaryLevel =>
    exists_xiContinuousHarmonic_of_step_contraction system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate (zero_lt_one.trans rateGreaterThanOne)
      resistanceVector vectorPositive eigenpair contractionFactor factorPositive factorStrict stepContraction
      boundaryLevel (target.val ∘ xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair boundaryLevel)
  let values : xiWeightedEnergyDomain system resistanceRate (zero_lt_one.trans rateGreaterThanOne)
      resistanceVector vectorPositive :=
    ⟨target.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, target.property⟩
  let energy := (xiExtendedWeightedEnergy system resistanceRate (zero_lt_one.trans rateGreaterThanOne)
    resistanceVector vectorPositive values.val).toReal
  have tailSquared := pow_le_pow_left₀ (norm_nonneg (approximation level - target.val))
    (tailBound target approximation approximationAgreement level) 2
  have factorSquared : (Real.sqrt resistanceRate⁻¹ ^ level) ^ 2 = (resistanceRate ^ level)⁻¹ := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, Real.sq_sqrt (inv_pos.mpr
      (zero_lt_one.trans rateGreaterThanOne)).le, inv_pow]
  rw [mul_pow, mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg, factorSquared] at tailSquared
  have coarseBound := xiUnion_edge_square_energy_bound system resistanceRate
    (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive values level edge
  have onDescendants : ∀ vertex ∈ xiDescendantCellVertices system level edge,
      (target.val (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) -
        target.val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level terminal)) ^ 2 ≤
      2 * (tailConstant ^ 2 + ∑ colour, resistanceVector colour) / resistanceRate ^ level * energy := by
    intro vertex vertexMembership
    have harmonicRange := xiHarmonic_union_cell_range system rulesConnected resistanceRate
      (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive eigenpair level
      (target.val ∘ xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level)
      (xiHarmonicUnionExtension system rulesConnected resistanceRate (zero_lt_one.trans rateGreaterThanOne)
        resistanceVector vectorPositive eigenpair level
        (target.val ∘ xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level))
      (xiHarmonicUnionExtension_values system rulesConnected resistanceRate (zero_lt_one.trans rateGreaterThanOne)
        resistanceVector vectorPositive eigenpair level _) edge vertex vertexMembership
    rw [← approximationAgreement level vertex] at harmonicRange
    have harmonicBound :
        (approximation level (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) -
          target.val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level terminal)) ^ 2 ≤
        (∑ colour, resistanceVector colour) / resistanceRate ^ level * energy := by
      rcases terminalMembership with rfl | rfl
      · have harmonicSquare := square_distance_to_endpoint_le _ _ _ harmonicRange.1 harmonicRange.2
        dsimp only [energy, values, xiCompletionEmbedding, Function.comp_apply] at coarseBound harmonicSquare ⊢
        nlinarith
      · have reversed := square_distance_to_endpoint_le _ _ _
          (by simpa only [min_comm] using harmonicRange.1)
          (by simpa only [max_comm] using harmonicRange.2)
        exact reversed.trans coarseBound
    have pointError := (approximation level - target.val).norm_coe_le_norm
      (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex)
    have pointErrorSquared := (pow_le_pow_left₀ (norm_nonneg _) pointError 2).trans tailSquared
    simp only [ContinuousMap.sub_apply, Real.norm_eq_abs, sq_abs] at pointErrorSquared
    have split := sq_nonneg
      ((target.val (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) -
        approximation level (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex)) -
       (approximation level (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) -
        target.val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level terminal)))
    dsimp only [energy, values] at *
    simp only [div_eq_mul_inv] at *
    nlinarith
  have closedBound : IsClosed {varying |
      (target.val varying - target.val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive
        distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level terminal)) ^ 2 ≤
      2 * (tailConstant ^ 2 + ∑ colour, resistanceVector colour) / resistanceRate ^ level * energy} :=
    isClosed_le ((target.val.continuous.sub continuous_const).pow 2) continuous_const
  apply closure_minimal (s := xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair '' xiDescendantCellVertices system level edge)
    (t := {varying | (target.val varying - target.val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level terminal)) ^ 2 ≤
      2 * (tailConstant ^ 2 + ∑ colour, resistanceVector colour) / resistanceRate ^ level * energy})
    ?_ closedBound pointMembership
  rintro _ ⟨vertex, membership, rfl⟩
  exact onDescendants vertex membership

end Completion
end
end EIGS

#print axioms EIGS.xiUnion_edge_square_energy_bound
#print axioms EIGS.exists_xiPhysicalClosedCell_point_terminal_energy_bound
