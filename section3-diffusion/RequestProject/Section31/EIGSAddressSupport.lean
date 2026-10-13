import RequestProject.Section31.EIGSSpeedWeakLimit
import RequestProject.Section31.EIGSFiniteHausdorff
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Every actual completion neighbourhood contains a positive address
cylinder. Full support is derived from incident edges and finite parent nets. -/

namespace EIGS

open MeasureTheory Filter Topology Metric Set

variable {K : ℕ}

instance xiVtxNontrivial (system : EIGSData K) (level : ℕ) : Nontrivial (XiVtx system level) := by
  induction level with
  | zero => exact inferInstanceAs (Nontrivial Bool)
  | succ level induction_hypothesis =>
    change Nontrivial (XiVtx system level ⊕ _)
    rcases induction_hypothesis.exists_pair_ne with ⟨first, second, distinct⟩
    exact ⟨⟨Sum.inl first, Sum.inl second, fun equality => distinct (Sum.inl.inj equality)⟩⟩

theorem xiVertex_has_incident_edge (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (level : ℕ) (vertex : XiVtx system level) :
    ∃ edge : XiEdge system.toRuleData level,
      XiTail system level edge = vertex ∨ XiHead system level edge = vertex := by
  obtain ⟨neighbor, adjacency⟩ := (xiSimpleGraph_connected system connected level).preconnected.exists_adj_of_nontrivial vertex
  change vertex ≠ neighbor ∧
    ((∃ edge, XiTail system level edge = vertex ∧ XiHead system level edge = neighbor) ∨
      (∃ edge, XiTail system level edge = neighbor ∧ XiHead system level edge = vertex)) at adjacency
  rcases adjacency.2 with ⟨edge, tailEquality, _⟩ | ⟨edge, _, headEquality⟩
  · exact ⟨edge, Or.inl tailEquality⟩
  · exact ⟨edge, Or.inr headEquality⟩

noncomputable def xiMaximumColourLength (system : EIGSData K) (lengths : Fin K → ℝ) : ℝ :=
  Finset.univ.sup' ⟨system.initCol, Finset.mem_univ _⟩ lengths

theorem xiColourLength_le_maximum (system : EIGSData K) (lengths : Fin K → ℝ) (colour : Fin K) :
    lengths colour ≤ xiMaximumColourLength system lengths :=
  Finset.le_sup' lengths (Finset.mem_univ colour)

variable (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)

theorem xiAddressLimit_near_vertex (mass : XiMassParameters system) (level : ℕ)
    (vertex : XiVtx system level) :
    ∃ address : XiEdgeAddress system,
      dist (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex)
        (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair address) ≤
      rate⁻¹ ^ level * xiMaximumColourLength system lengths +
        (xiRuleRadius system lengths * rate⁻¹) * rate⁻¹ ^ level / (1 - rate⁻¹) := by
  obtain ⟨edge, incidence⟩ := xiVertex_has_incident_edge system connected level vertex
  obtain ⟨address, addressEquality⟩ := mass.exists_address_through_edge level edge
  have maximumNonnegative : 0 ≤ xiMaximumColourLength system lengths :=
    (lengthsPositive system.initCol).le.trans (xiColourLength_le_maximum system lengths system.initCol)
  have endpointBound :
      dist (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex)
        (xiEdgeTailPoint system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair level edge) ≤
      rate⁻¹ ^ level * xiMaximumColourLength system lengths := by
    rcases incidence with tailEquality | headEquality
    · rw [← tailEquality]
      change dist _ _ ≤ _
      simpa only [xiEdgeTailPoint, dist_self] using
        (mul_nonneg (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le)) level) maximumNonnegative)
    · rw [← headEquality]
      change dist (xiEdgeHeadPoint system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair level edge)
        (xiEdgeTailPoint system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair level edge) ≤ _
      rw [dist_comm]
      exact (xiCompletionEdge_distance_le system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair level edge).trans
        (mul_le_mul_of_nonneg_left (xiColourLength_le_maximum system lengths _)
          (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le)) level))
  have addressBound := xiAddressLimit_error system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair address level
  have tailEquality : xiAddressTailApproximation system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level address =
      xiEdgeTailPoint system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair level edge := by
    simp only [xiAddressTailApproximation, xiEdgeTailPoint, addressEquality]
  rw [tailEquality] at addressBound
  exact ⟨address, (dist_triangle _ _ _).trans (add_le_add endpointBound addressBound)⟩

theorem xiAddressLimit_denseRange (mass : XiMassParameters system) :
    DenseRange (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) := by
  apply Metric.denseRange_iff.mpr
  intro point tolerance tolerancePositive
  have powerConvergence := tendsto_pow_atTop_nhds_zero_of_lt_one
    (inv_nonneg.mpr (zero_le_one.trans rateGreaterThanOne.le))
    ((inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne)
  have errorConvergence :=
    ((xiFiniteNetRadius_tendsto_zero system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair).add
      (powerConvergence.mul_const (xiMaximumColourLength system lengths))).add
      (xiAddressError_tendsto_zero system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
  simp only [zero_mul, zero_add, add_zero] at errorConvergence
  obtain ⟨level, levelBound⟩ := (errorConvergence.eventually (gt_mem_nhds tolerancePositive)).exists
  obtain ⟨vertex, vertexBound⟩ := xiCompletion_finite_net system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair level point
  obtain ⟨address, addressBound⟩ := xiAddressLimit_near_vertex system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level vertex
  refine ⟨address, ?_⟩
  have triangle := dist_triangle point
    (xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex)
    (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair address)
  linarith only [triangle, vertexBound, addressBound, levelBound]

theorem xiLimitMeasure_ball_positive (mass : XiMassParameters system)
    (point : XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) {radius : ℝ} (radiusPositive : 0 < radius) :
    0 < xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass (ball point radius) := by
  obtain ⟨reference, referenceBound⟩ := Metric.denseRange_iff.mp
    (xiAddressLimit_denseRange system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
    point (radius / 2) (half_pos radiusPositive)
  have diameterConvergence := (xiAddressError_tendsto_zero system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair).const_mul 2
  simp only [mul_zero] at diameterConvergence
  obtain ⟨level, levelBound⟩ := (diameterConvergence.eventually (gt_mem_nhds (half_pos radiusPositive))).exists
  have cylinderPositive : 0 < mass.addressMeasure
      {address | xiAddressEdge system level address = xiAddressEdge system level reference} := by
    rw [mass.addressMeasure_cylinder]
    exact ENNReal.ofReal_pos.mpr (mass.edgeWeight_positive level _)
  rw [xiLimitMeasure, Measure.map_apply
    (measurable_xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) measurableSet_ball]
  apply cylinderPositive.trans_le
  apply measure_mono
  intro address agreement
  have close := xiAddressLimits_same_edge_close system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair level reference address agreement.symm
  have triangle := dist_triangle point
    (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair reference)
    (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair address)
  change dist _ point < radius
  rw [dist_comm]
  linarith only [triangle, referenceBound, close, levelBound]

instance xiLimitMeasure_isOpenPosMeasure (mass : XiMassParameters system) :
    (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).IsOpenPosMeasure where
  open_pos := by
    intro openSet openSetOpen openSetNonempty
    obtain ⟨point, pointMembership⟩ := openSetNonempty
    obtain ⟨radius, radiusPositive, ballSubset⟩ := Metric.isOpen_iff.mp openSetOpen point pointMembership
    exact ne_of_gt ((xiLimitMeasure_ball_positive system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass point radiusPositive).trans_le (measure_mono ballSubset))

end EIGS

#print axioms EIGS.xiVertex_has_incident_edge
#print axioms EIGS.xiAddressLimit_near_vertex
#print axioms EIGS.xiAddressLimit_denseRange
#print axioms EIGS.xiLimitMeasure_ball_positive
#print axioms EIGS.xiLimitMeasure_isOpenPosMeasure
