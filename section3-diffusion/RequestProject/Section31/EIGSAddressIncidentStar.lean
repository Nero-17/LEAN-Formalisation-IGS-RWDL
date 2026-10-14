import RequestProject.Section31.EIGSAddressHarmonicCellEnergy
import RequestProject.Section31.EIGSAddressSupport
import RequestProject.Section31.EIGSIncidentStarCompletionMesh

/-! The actual address star, counted with endpoint multiplicity. Its mass is
comparable to incidence times the cell mass, and every address in its support
lies near the same actual finite vertex. Multiplicity avoids any disjointness
assumption about images of cells in the completion. Candidate; not compiled. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

def xiEdgeStarMultiplicity (system : EIGSData K) (level : ℕ)
    (vertex : XiVtx system level) (edge : XiEdge system.toRuleData level) : ℝ :=
  (if XiTail system level edge = vertex then 1 else 0) +
    (if XiHead system level edge = vertex then 1 else 0)

def xiAddressStarWeight (system : EIGSData K) (level : ℕ)
    (vertex : XiVtx system level) (address : XiEdgeAddress system) : ℝ :=
  xiEdgeStarMultiplicity system level vertex (xiAddressEdge system level address)

theorem xiEdgeStarMultiplicity_bounds (system : EIGSData K) (level : ℕ)
    (vertex : XiVtx system level) (edge : XiEdge system.toRuleData level) :
    0 ≤ xiEdgeStarMultiplicity system level vertex edge ∧
      xiEdgeStarMultiplicity system level vertex edge ≤ 2 := by
  unfold xiEdgeStarMultiplicity
  split_ifs <;> norm_num

theorem xiEdgeStarMultiplicity_sum (system : EIGSData K) (level : ℕ)
    (vertex : XiVtx system level) :
    ∑ edge, xiEdgeStarMultiplicity system level vertex edge =
      (xiVertexIncidenceCount system level vertex : ℝ) := by
  simp only [xiEdgeStarMultiplicity, xiVertexIncidenceCount, Nat.cast_add,
    Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_add_distrib]

theorem xiAddressStarWeight_integral (system : EIGSData K) (mass : XiMassParameters system)
    (level : ℕ) (vertex : XiVtx system level) :
    (∫ address, xiAddressStarWeight system level vertex address ∂mass.addressMeasure) =
      ∑ edge, mass.edgeWeight level edge * xiEdgeStarMultiplicity system level vertex edge :=
  xiAddress_coordinate_integral system mass level (xiEdgeStarMultiplicity system level vertex)

theorem exists_xiAddressStarWeight_mass_comparison (system : EIGSData K)
    (mass : XiMassParameters system) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ level (vertex : XiVtx system level),
      lower / mass.rate ^ level * (xiVertexIncidenceCount system level vertex : ℝ) ≤
        (∫ address, xiAddressStarWeight system level vertex address ∂mass.addressMeasure) ∧
      (∫ address, xiAddressStarWeight system level vertex address ∂mass.addressMeasure) ≤
        upper / mass.rate ^ level * (xiVertexIncidenceCount system level vertex : ℝ) := by
  obtain ⟨minimumColour, _, minimumBound⟩ := Finset.univ.exists_min_image mass.amplitude
    ⟨system.initCol, Finset.mem_univ _⟩
  have sumPositive : 0 < ∑ colour, mass.amplitude colour :=
    (mass.amplitude_positive system.initCol).trans_le
      (Finset.single_le_sum (fun colour _ => (mass.amplitude_positive colour).le)
        (Finset.mem_univ system.initCol))
  refine ⟨mass.amplitude minimumColour / mass.amplitude system.initCol,
    (∑ colour, mass.amplitude colour) / mass.amplitude system.initCol,
    div_pos (mass.amplitude_positive _) (mass.amplitude_positive _),
    div_pos sumPositive (mass.amplitude_positive _), ?_⟩
  intro level vertex
  have lowerBound (edge : XiEdge system.toRuleData level) :
      (mass.amplitude minimumColour / mass.amplitude system.initCol) / mass.rate ^ level ≤
        mass.edgeWeight level edge := by
    rw [XiMassParameters.edgeWeight, div_div, mul_comm (mass.amplitude system.initCol)]
    exact div_le_div_of_nonneg_right (minimumBound _ (Finset.mem_univ _)) (by positivity)
  have upperBound (edge : XiEdge system.toRuleData level) :
      mass.edgeWeight level edge ≤
        ((∑ colour, mass.amplitude colour) / mass.amplitude system.initCol) / mass.rate ^ level := by
    rw [XiMassParameters.edgeWeight, div_div, mul_comm (mass.amplitude system.initCol)]
    exact div_le_div_of_nonneg_right
      (Finset.single_le_sum (fun colour _ => (mass.amplitude_positive colour).le) (Finset.mem_univ _))
      (by positivity)
  rw [xiAddressStarWeight_integral, ← xiEdgeStarMultiplicity_sum]
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun edge _ =>
      mul_le_mul_of_nonneg_right (lowerBound edge) (xiEdgeStarMultiplicity_bounds system level vertex edge).1
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun edge _ =>
      mul_le_mul_of_nonneg_right (upperBound edge) (xiEdgeStarMultiplicity_bounds system level vertex edge).1

theorem xiAddressStarWeight_support_mesh (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (level : ℕ) (vertex : XiVtx system level) (address : XiEdgeAddress system)
    (supported : xiAddressStarWeight system level vertex address ≠ 0) :
    dist (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair address)
      (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair level vertex) ≤
      (xiMaximumColourLength system lengths +
        (xiRuleRadius system lengths * distanceRate⁻¹) / (1 - distanceRate⁻¹)) * distanceRate⁻¹ ^ level := by
  have incidence : XiTail system level (xiAddressEdge system level address) = vertex ∨
      XiHead system level (xiAddressEdge system level address) = vertex := by
    by_contra neither
    push_neg at neither
    exact supported (by simp only [xiAddressStarWeight, xiEdgeStarMultiplicity,
      if_neg neither.1, if_neg neither.2, zero_add])
  have maximumNonnegative : 0 ≤ xiMaximumColourLength system lengths :=
    (lengthsPositive system.initCol).le.trans (xiColourLength_le_maximum system lengths system.initCol)
  have endpointBound : dist
      (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair level vertex)
      (xiAddressTailApproximation system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair level address) ≤
      distanceRate⁻¹ ^ level * xiMaximumColourLength system lengths := by
    rcases incidence with tail | head
    · rw [← tail]
      change dist _ _ ≤ _
      simpa only [xiAddressTailApproximation, dist_self] using
        mul_nonneg (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans distanceGreaterThanOne).le) level) maximumNonnegative
    · rw [← head]
      change dist (xiEdgeHeadPoint system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair level (xiAddressEdge system level address))
        (xiEdgeTailPoint system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair level (xiAddressEdge system level address)) ≤ _
      rw [dist_comm]
      exact (xiCompletionEdge_distance_le system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair level _).trans
        (mul_le_mul_of_nonneg_left (xiColourLength_le_maximum system lengths _)
          (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans distanceGreaterThanOne).le) level))
  have errorBound := xiAddressLimit_error system rulesConnected lengths lengthsPositive distanceRate
    distanceGreaterThanOne metricEigenpair address level
  rw [dist_comm]
  exact ((dist_triangle _ _ _).trans (add_le_add endpointBound errorBound)).trans_eq (by ring)

end
end EIGS

#print axioms EIGS.xiEdgeStarMultiplicity_bounds
#print axioms EIGS.xiEdgeStarMultiplicity_sum
#print axioms EIGS.xiAddressStarWeight_integral
#print axioms EIGS.exists_xiAddressStarWeight_mass_comparison
#print axioms EIGS.xiAddressStarWeight_support_mesh
