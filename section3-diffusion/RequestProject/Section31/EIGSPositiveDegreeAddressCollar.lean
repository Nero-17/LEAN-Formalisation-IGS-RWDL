import RequestProject.Section31.EIGSAddressEndpointCollar
import RequestProject.Section31.EIGSPositiveDegreeSpectralData

/-! Actual collar/incidence estimates from a positive normalized degree eigenpair.
The original address measure and oriented rule graphs are unchanged. Candidate. -/

namespace EIGS
open MeasureTheory Filter Matrix
open scoped Classical BigOperators Topology ENNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_uniform_xiIncidence_growth_upper_of_positive_degree_data (system : EIGSData K)
    (degreeData : XiPositiveDegreeSpectralData system) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ birth age (vertex : XiVtx system birth),
      (xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) ≤
        coefficient * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age *
          (xiVertexIncidenceCount system birth vertex : ℝ) := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  let weights := degreeData.vector
  have weightsPositive := degreeData.positive
  have ratePositive := zero_lt_one.trans degreeData.rate_gt_one
  have normalized := degreeData.normalized
  have eigenpair := degreeData.eigenpair
  obtain ⟨minimumState, _, minimumBound⟩ := Finset.univ.exists_min_image weights Finset.univ_nonempty
  refine ⟨(weights minimumState)⁻¹, inv_pos.mpr (weightsPositive _), ?_⟩
  intro birth age vertex
  have weightedIdentity : ∀ steps,
      (∑ state, degVec system (birth + steps) (xiForward system birth steps vertex) state * weights state) =
        (∑ state, degVec system birth vertex state * weights state) *
          finiteRealMatrixSpectralRadius (degreeMatrix system) ^ steps := by
    intro steps
    induction steps with
    | zero => simp only [Nat.add_zero, xiForward, id_eq, pow_zero, mul_one]
    | succ steps induction =>
      rw [degVec_xiForward_succ]
      change Matrix.vecMul (degVec system (birth + steps) (xiForward system birth steps vertex))
        (degreeMatrix system) ⬝ᵥ weights = _
      rw [← Matrix.dotProduct_mulVec, eigenpair]
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
      calc
        _ = finiteRealMatrixSpectralRadius (degreeMatrix system) *
            (∑ state, degVec system (birth + steps) (xiForward system birth steps vertex) state * weights state) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro state _
          ring
        _ = _ := by rw [induction, pow_succ]; ring
  have initialBound : (∑ state, degVec system birth vertex state * weights state) ≤
      ∑ state, degVec system birth vertex state := by
    have atMostOne (state : Fin K ⊕ Fin K) : weights state ≤ 1 := by
      rw [← normalized]
      exact Finset.single_le_sum (fun other _ => (weightsPositive other).le) (Finset.mem_univ _)
    apply Finset.sum_le_sum
    intro state _
    have nonnegative : 0 ≤ degVec system birth vertex state := by
      cases state <;> exact Nat.cast_nonneg _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (atMostOne state) nonnegative
  have minimumWeighted : weights minimumState *
      (∑ state, degVec system (birth + age) (xiForward system birth age vertex) state) ≤
        ∑ state, degVec system (birth + age) (xiForward system birth age vertex) state * weights state := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro state _
    have nonnegative : 0 ≤ degVec system (birth + age) (xiForward system birth age vertex) state := by
      cases state <;> exact Nat.cast_nonneg _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (minimumBound state (Finset.mem_univ _)) nonnegative
  rw [weightedIdentity] at minimumWeighted
  have bound := minimumWeighted.trans
    (mul_le_mul_of_nonneg_right initialBound (pow_pos ratePositive age).le)
  rw [xiVertexIncidenceCount_eq_degree_state_sum, xiVertexIncidenceCount_eq_degree_state_sum]
  calc
    _ ≤ (∑ state, degVec system birth vertex state) *
        finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age / weights minimumState :=
      (le_div_iff₀ (weightsPositive minimumState)).mpr (by simpa only [mul_comm] using bound)
    _ = _ := by rw [div_eq_mul_inv]; ring

theorem exists_xiAddressEndpointCollar_mass_bound_of_positive_degree_data (system : EIGSData K)
    (mass : XiMassParameters system) (degreeData : XiPositiveDegreeSpectralData system) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ coarse width,
      mass.addressMeasure (xiAddressEndpointCollar system coarse width) ≤
        ENNReal.ofReal (coefficient *
          (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) ^ width) := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  have degreePositive := zero_lt_one.trans degreeData.rate_gt_one
  obtain ⟨degreeConstant, degreeConstantPositive, degreeBound⟩ :=
    exists_uniform_xiIncidence_growth_upper_of_positive_degree_data system degreeData
  obtain ⟨_, starConstant, _, starConstantPositive, starBounds⟩ :=
    exists_xiAddressStarWeight_mass_comparison system mass
  obtain ⟨minimumColour, _, minimumBound⟩ := Finset.univ.exists_min_image mass.amplitude
    ⟨system.initCol, Finset.mem_univ _⟩
  have minimumPositive := mass.amplitude_positive minimumColour
  have initialPositive := mass.amplitude_positive system.initCol
  have massRatePositive := mass.rate_positive
  refine ⟨2 * starConstant * degreeConstant * mass.amplitude system.initCol / mass.amplitude minimumColour,
    by positivity, ?_⟩
  intro coarse width
  have edgeCountBound : (totalEdges system.toRuleData coarse : ℝ) ≤
      mass.rate ^ coarse * mass.amplitude system.initCol / mass.amplitude minimumColour := by
    apply (le_div_iff₀ (mass.amplitude_positive minimumColour)).mpr
    rw [← mass.sum_edge_amplitudes coarse]
    change (Fintype.card (XiEdge system.toRuleData coarse) : ℝ) * mass.amplitude minimumColour ≤ _
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (fun (edge : XiEdge system.toRuleData coarse) _ =>
        minimumBound (XiCol system.toRuleData coarse edge) (Finset.mem_univ _)))
  have starIntegrable (vertex : XiVtx system coarse) : Integrable
      (xiAddressStarWeight system (coarse + width) (xiForward system coarse width vertex)) mass.addressMeasure :=
    (show Integrable (xiEdgeStarMultiplicity system (coarse + width) (xiForward system coarse width vertex))
      (mass.addressMeasure.map (xiAddressEdge system (coarse + width))) from Integrable.of_finite).comp_measurable
        (measurable_xiAddressEdge system (coarse + width))
  have indicatorBound (address : XiEdgeAddress system) :
      (xiAddressEndpointCollar system coarse width).indicator (fun _ => (1 : ℝ)) address ≤
        ∑ vertex : XiVtx system coarse,
          xiAddressStarWeight system (coarse + width) (xiForward system coarse width vertex) address := by
    by_cases member : address ∈ xiAddressEndpointCollar system coarse width
    · rw [Set.indicator_of_mem member]
      obtain ⟨vertex, nonzero⟩ := member
      have oneBelow : 1 ≤ xiAddressStarWeight system (coarse + width) (xiForward system coarse width vertex) address := by
        unfold xiAddressStarWeight xiEdgeStarMultiplicity at nonzero ⊢
        split_ifs at * <;> norm_num at *
      exact oneBelow.trans (Finset.single_le_sum
        (fun other _ => (xiEdgeStarMultiplicity_bounds system (coarse + width)
          (xiForward system coarse width other) _).1) (Finset.mem_univ _))
    · rw [Set.indicator_of_notMem member]
      exact Finset.sum_nonneg fun vertex _ => (xiEdgeStarMultiplicity_bounds system (coarse + width)
        (xiForward system coarse width vertex) _).1
  have integralBound := integral_mono
    ((integrable_const (1 : ℝ)).indicator (measurableSet_xiAddressEndpointCollar system coarse width))
    (integrable_finset_sum _ (fun vertex _ => starIntegrable vertex)) indicatorBound
  rw [integral_indicator_const (1 : ℝ) (measurableSet_xiAddressEndpointCollar system coarse width),
    smul_eq_mul, mul_one,
    integral_finset_sum _ (fun vertex _ => starIntegrable vertex)] at integralBound
  have starSumBound : (∑ vertex : XiVtx system coarse,
      ∫ address, xiAddressStarWeight system (coarse + width) (xiForward system coarse width vertex) address
        ∂mass.addressMeasure) ≤
      starConstant / mass.rate ^ (coarse + width) *
        (degreeConstant * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ width *
          (2 * (totalEdges system.toRuleData coarse : ℝ))) := by
    calc
      _ ≤ ∑ vertex : XiVtx system coarse,
          starConstant / mass.rate ^ (coarse + width) *
            (degreeConstant * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ width *
              (xiVertexIncidenceCount system coarse vertex : ℝ)) := by
        apply Finset.sum_le_sum
        intro vertex _
        exact ((starBounds (coarse + width) (xiForward system coarse width vertex)).2).trans
          (mul_le_mul_of_nonneg_left (degreeBound coarse width vertex) (by positivity))
      _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum, xiVertexIncidenceCount_sum]
  have realBound := integralBound.trans starSumBound
  have edgeBound := mul_le_mul_of_nonneg_left edgeCountBound
    (show 0 ≤ starConstant / mass.rate ^ (coarse + width) *
      (degreeConstant * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ width * 2) by
      positivity)
  have finalBound : mass.addressMeasure.real (xiAddressEndpointCollar system coarse width) ≤
      (2 * starConstant * degreeConstant * mass.amplitude system.initCol / mass.amplitude minimumColour) *
        (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) ^ width := by
    calc
      _ ≤ starConstant / mass.rate ^ (coarse + width) *
          (degreeConstant * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ width *
            (2 * (mass.rate ^ coarse * mass.amplitude system.initCol / mass.amplitude minimumColour))) := by
        exact realBound.trans (by nlinarith only [edgeBound])
      _ = _ := by
        rw [pow_add, div_pow]
        field_simp [mass.rate_positive.ne', (mass.amplitude_positive minimumColour).ne']
        <;> ring
  have measureEquality : ENNReal.ofReal
      (mass.addressMeasure.real (xiAddressEndpointCollar system coarse width)) =
        mass.addressMeasure (xiAddressEndpointCollar system coarse width) := ofReal_measureReal
  exact measureEquality.symm.trans_le (ENNReal.ofReal_le_ofReal finalBound)

end
end EIGS

#print axioms EIGS.exists_uniform_xiIncidence_growth_upper_of_positive_degree_data
#print axioms EIGS.exists_xiAddressEndpointCollar_mass_bound_of_positive_degree_data

