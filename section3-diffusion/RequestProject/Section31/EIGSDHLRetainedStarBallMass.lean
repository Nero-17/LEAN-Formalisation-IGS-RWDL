import RequestProject.Section31.EIGSDHLRetentionBlockGeometry
import RequestProject.Section31.EIGSFlowerDegreeSpectrum
import RequestProject.Section31.EIGSDegreeEigenweight
import RequestProject.Section31.EIGSIncidenceResistanceDecayWithoutPrimitive
import RequestProject.Section31.EIGSNativeDiscreteEnergy
import RequestProject.Section31.EIGSVertexStarBallMassLower

/-! A retained DHL terminal has actual incidence at least 2^age. Its entire
fine incident star lies in a ball at the cell scale, also when the ball is
centred at the coded point rather than the terminal. -/

namespace EIGS
open MeasureTheory Metric
open scoped Classical BigOperators
noncomputable section

theorem dhlVertexIncidence_forward (coarse age : ℕ) (vertex : XiVtx (flowerSystem 2 2) coarse) :
    (xiVertexIncidenceCount (flowerSystem 2 2) (coarse + age)
      (xiForward (flowerSystem 2 2) coarse age vertex) : ℝ) =
        (2 : ℝ) ^ age * (xiVertexIncidenceCount (flowerSystem 2 2) coarse vertex : ℝ) := by
  have identity := degree_eigenweight_forward (flowerSystem 2 2) (fun _ => 1) 2
    (by simpa using flowerSystem_degree_positive_eigenpair 2 2 (by norm_num) (by norm_num))
    coarse age vertex
  simpa only [mul_one, ← xiVertexIncidenceCount_eq_degree_state_sum] using identity

theorem dhlVertexIncidence_forward_lower (coarse age : ℕ)
    (vertex : XiVtx (flowerSystem 2 2) coarse) :
    (2 : ℝ) ^ age ≤ (xiVertexIncidenceCount (flowerSystem 2 2) (coarse + age)
      (xiForward (flowerSystem 2 2) coarse age vertex) : ℝ) := by
  rw [dhlVertexIncidence_forward]
  have positive := xiVertexIncidenceCount_positive (flowerSystem 2 2)
    (flowerSystem_connected 2 2 (by norm_num) (by norm_num)) coarse vertex
  have aboveOne : (1 : ℝ) ≤ (xiVertexIncidenceCount (flowerSystem 2 2) coarse vertex : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt positive)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left aboveOne (by positivity : (0 : ℝ) ≤ 2 ^ age)

theorem exists_dhlRetainedStarBallMassLower
    (connected : ∀ colour, (ruleSG (flowerSystem 2 2) colour).Connected)
    (lengths : Fin 1 → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : ((flowerSystem 2 2).ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters (flowerSystem 2 2)) :
    ∃ coefficient radiusFactor : ℝ, 0 < coefficient ∧ 0 < radiusFactor ∧
      ∀ coarse age (vertex : XiVtx (flowerSystem 2 2) coarse)
        (address : XiEdgeAddress (flowerSystem 2 2)),
        (XiTail (flowerSystem 2 2) (coarse + age)
            (xiAddressEdge (flowerSystem 2 2) (coarse + age) address) =
              xiForward (flowerSystem 2 2) coarse age vertex ∨
          XiHead (flowerSystem 2 2) (coarse + age)
            (xiAddressEdge (flowerSystem 2 2) (coarse + age) address) =
              xiForward (flowerSystem 2 2) coarse age vertex) →
        coefficient / mass.rate ^ (coarse + age) * (2 : ℝ) ^ age ≤
          (xiLimitMeasure (flowerSystem 2 2) connected lengths lengthsPositive rate
            rateGreaterThanOne eigenpair mass).real
            (Metric.ball (xiAddressLimit (flowerSystem 2 2) connected lengths lengthsPositive rate
              rateGreaterThanOne eigenpair address) (radiusFactor * rate⁻¹ ^ (coarse + age))) := by
  obtain ⟨coefficient, starRadius, coefficientPositive, starRadiusPositive, starLower⟩ :=
    exists_xiVertexStarBallMassLower (flowerSystem 2 2) connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass
  let mesh := xiMaximumColourLength (flowerSystem 2 2) lengths +
    (xiRuleRadius (flowerSystem 2 2) lengths * rate⁻¹) / (1 - rate⁻¹)
  have meshNonnegative : 0 ≤ mesh := by
    exact add_nonneg
      ((lengthsPositive (flowerSystem 2 2).initCol).le.trans
        (xiColourLength_le_maximum (flowerSystem 2 2) lengths _))
      (div_nonneg (mul_nonneg
        (xiRuleRadius_nonnegative (flowerSystem 2 2) (fun colour => (lengthsPositive colour).le))
        (inv_nonneg.mpr (zero_lt_one.trans rateGreaterThanOne).le))
        (sub_pos.mpr (inv_lt_one_of_one_lt₀ rateGreaterThanOne)).le)
  refine ⟨coefficient, starRadius + mesh + 1, coefficientPositive, by positivity, ?_⟩
  intro coarse age vertex address incident
  have supported : xiAddressStarWeight (flowerSystem 2 2) (coarse + age)
      (xiForward (flowerSystem 2 2) coarse age vertex) address ≠ 0 := by
    rcases incident with tail | head
    · simp only [xiAddressStarWeight, xiEdgeStarMultiplicity, tail, if_true]
      split_ifs <;> norm_num
    · simp only [xiAddressStarWeight, xiEdgeStarMultiplicity, head, if_true]
      split_ifs <;> norm_num
  have near := xiAddressStarWeight_support_mesh (flowerSystem 2 2) connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair (coarse + age) (xiForward (flowerSystem 2 2) coarse age vertex)
    address supported
  have ballSubset : Metric.ball
      (xiCompletionEmbedding (flowerSystem 2 2) connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarse + age)
          (xiForward (flowerSystem 2 2) coarse age vertex)) (starRadius * rate⁻¹ ^ (coarse + age)) ⊆
      Metric.ball (xiAddressLimit (flowerSystem 2 2) connected lengths lengthsPositive rate
        rateGreaterThanOne eigenpair address) ((starRadius + mesh + 1) * rate⁻¹ ^ (coarse + age)) := by
    intro point inside
    have triangle := dist_triangle point
      (xiCompletionEmbedding (flowerSystem 2 2) connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair (coarse + age)
          (xiForward (flowerSystem 2 2) coarse age vertex))
      (xiAddressLimit (flowerSystem 2 2) connected lengths lengthsPositive rate rateGreaterThanOne eigenpair address)
    rw [dist_comm] at near
    change dist _ _ < _ at inside ⊢
    change dist _ _ ≤ mesh * rate⁻¹ ^ (coarse + age) at near
    have powerPositive := pow_pos (inv_pos.mpr (zero_lt_one.trans rateGreaterThanOne)) (coarse + age)
    nlinarith
  exact (mul_le_mul_of_nonneg_left (dhlVertexIncidence_forward_lower coarse age vertex)
    (div_pos coefficientPositive (pow_pos mass.rate_positive (coarse + age))).le).trans
      ((starLower (coarse + age) (xiForward (flowerSystem 2 2) coarse age vertex)).trans
        (measureReal_mono ballSubset))

end
end EIGS

#print axioms EIGS.dhlVertexIncidence_forward
#print axioms EIGS.dhlVertexIncidence_forward_lower
#print axioms EIGS.exists_dhlRetainedStarBallMassLower
