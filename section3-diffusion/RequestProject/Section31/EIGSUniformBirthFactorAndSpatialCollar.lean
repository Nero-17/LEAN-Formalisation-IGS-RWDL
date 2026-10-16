import RequestProject.Section31.EIGSMetricOfRules
import RequestProject.Section31.EIGSEdgeAddressMeasure
import RequestProject.Section31.BallMassDiameterScaling
import RequestProject.Section31.EIGSOriginalCountableRealisation
import RequestProject.Section31.EIGSAddressCellMetricSeparation
import RequestProject.Section31.EIGSAddressEndpointCollar
import RequestProject.Section31.EIGSVertexStarBallMassLower
import RequestProject.Section31.EIGSUniformVertexIncidenceBound


namespace EIGS
open MeasureTheory Filter Topology Metric Matrix
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem xiAddressLimit_vertex_separated_of_nonincident (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (lowerLength : ℝ) (lowerLengthPositive : 0 < lowerLength)
    (lengthLower : ∀ colour, lowerLength ≤ lengths colour)
    (level : ℕ) (vertex : XiVtx system level) (address : XiEdgeAddress system)
    (notTail : XiTail system level (xiAddressEdge system level address) ≠ vertex)
    (notHead : XiHead system level (xiAddressEdge system level address) ≠ vertex) :
    lowerLength * rate⁻¹ ^ level ≤
      dist (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex)
        (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair address) := by
  have ratePositive := zero_lt_one.trans rateGreaterThanOne
  have finiteBound (steps : ℕ) : lowerLength * rate⁻¹ ^ level ≤
      dist (xiCompletionEmbedding system connected lengths lengthsPositive rate ratePositive eigenpair level vertex)
        (xiAddressTailApproximation system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
          (level + steps) address) := by
    have radiusBound : ∀ colour,
        rate ^ steps * lowerLength ≤ ((system.ruleFamily connected).metricLengths^[steps] lengths) colour := by
      intro colour
      rw [system.metricLengths_iterate_eigenpair connected ratePositive.le eigenpair]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (lengthLower colour) (pow_nonneg ratePositive.le steps)
    have separation := xiWeightedDistance_cell_to_outside_two_stars system connected level steps
      (xiAddressEdge system level address) (fun colour => (lengthsPositive colour).le)
      (rate ^ steps * lowerLength) (mul_pos (pow_pos ratePositive steps) lowerLengthPositive)
      radiusBound (xiAddressEdge system (level + steps) address) (xiEdgeAncestor_address system level steps address)
      (xiForward system level steps vertex)
      (fun inside => notTail ((xiIncidentStar_forward_iff system level steps _ vertex).mp inside).symm)
      (fun inside => notHead ((xiIncidentStar_forward_iff system level steps _ vertex).mp inside).symm)
    have scaled := mul_le_mul_of_nonneg_left separation
      (pow_nonneg (inv_nonneg.mpr ratePositive.le) (level + steps))
    have cancellation : rate⁻¹ ^ (level + steps) * (rate ^ steps * lowerLength) =
        lowerLength * rate⁻¹ ^ level := by
      rw [pow_add]
      calc
        _ = (lowerLength * rate⁻¹ ^ level) * (rate⁻¹ ^ steps * rate ^ steps) := by ring
        _ = _ := by simp only [inv_pow, inv_mul_cancel₀ (pow_ne_zero steps ratePositive.ne'), mul_one]
    rw [cancellation] at scaled
    rw [← xiCompletionEmbedding_forward system connected lengths lengthsPositive rate ratePositive eigenpair level steps vertex]
    change _ ≤ dist _ (xiCompletionEmbedding system connected lengths lengthsPositive rate ratePositive eigenpair
      (level + steps) (XiTail system (level + steps) (xiAddressEdge system (level + steps) address)))
    rw [dist_comm, xiCompletionEmbedding_dist_eq_scaled_weighted]
    exact scaled
  exact ge_of_tendsto
    (tendsto_const_nhds.dist ((xiAddressTailApproximation_tendsto system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair address).comp (by
        simpa only [Nat.add_comm] using tendsto_add_atTop_nat level)))
    (Filter.Eventually.of_forall finiteBound)

theorem exists_xiVertexClosedBall_incidence_mass_upper (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system)
    (lowerLength : ℝ) (lowerLengthPositive : 0 < lowerLength)
    (lengthLower : ∀ colour, lowerLength ≤ lengths colour) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ level (vertex : XiVtx system level) radius,
      radius < lowerLength * rate⁻¹ ^ level →
      (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
        (Metric.closedBall (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex) radius) ≤
      coefficient / mass.rate ^ level * (xiVertexIncidenceCount system level vertex : ℝ) := by
  obtain ⟨_, coefficient, _, coefficientPositive, starBounds⟩ :=
    exists_xiAddressStarWeight_mass_comparison system mass
  refine ⟨coefficient, coefficientPositive, ?_⟩
  intro level vertex radius radiusSmall
  let region := (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) ⁻¹'
    Metric.closedBall (xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex) radius
  have regionMeasurable : MeasurableSet region := isClosed_closedBall.measurableSet.preimage
    (measurable_xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
  have starIntegrable : Integrable (xiAddressStarWeight system level vertex) mass.addressMeasure :=
    (show Integrable (xiEdgeStarMultiplicity system level vertex)
      (mass.addressMeasure.map (xiAddressEdge system level)) from Integrable.of_finite).comp_measurable
        (measurable_xiAddressEdge system level)
  have pointwise (address : XiEdgeAddress system) : region.indicator (fun _ => (1 : ℝ)) address ≤
      xiAddressStarWeight system level vertex address := by
    by_cases inside : address ∈ region
    · rw [Set.indicator_of_mem inside]
      have incidence : XiTail system level (xiAddressEdge system level address) = vertex ∨
          XiHead system level (xiAddressEdge system level address) = vertex := by
        by_contra neither
        have separated := xiAddressLimit_vertex_separated_of_nonincident system connected lengths lengthsPositive
          rate rateGreaterThanOne eigenpair lowerLength lowerLengthPositive lengthLower level vertex address
          (not_or.mp neither).1 (not_or.mp neither).2
        have near : dist (xiCompletionEmbedding system connected lengths lengthsPositive rate
            (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex)
            (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair address) ≤ radius := by
          simpa only [region, Set.mem_preimage, Metric.mem_closedBall, dist_comm] using inside
        exact (not_lt_of_ge separated) (near.trans_lt radiusSmall)
      rcases incidence with incidence | incidence <;>
        unfold xiAddressStarWeight xiEdgeStarMultiplicity <;>
        simp only [incidence, if_true] <;> split_ifs <;> norm_num
    · rw [Set.indicator_of_notMem inside]
      exact (xiEdgeStarMultiplicity_bounds system level vertex _).1
  have compared := integral_mono ((integrable_const (1 : ℝ)).indicator regionMeasurable) starIntegrable pointwise
  rw [integral_indicator_const (1 : ℝ) regionMeasurable, smul_eq_mul, mul_one] at compared
  have ballEquality :
      (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
        (Metric.closedBall (xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair level vertex) radius) = mass.addressMeasure.real region := by
    rw [xiLimitMeasure, measureReal_def, Measure.map_apply
      (measurable_xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
      isClosed_closedBall.measurableSet]
    rfl
  rw [ballEquality]
  exact compared.trans (starBounds level vertex).2

end
end EIGS
#print axioms EIGS.xiAddressLimit_vertex_separated_of_nonincident
#print axioms EIGS.exists_xiVertexClosedBall_incidence_mass_upper



namespace EIGS
open MeasureTheory Matrix
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def xiVertexBornAt (system : EIGSData K) : (birth : ℕ) → XiVtx system birth → Prop
  | 0, _ => True
  | birth + 1, vertex => ∀ old : XiVtx system birth, Sum.inl old ≠ vertex

theorem exists_xiUniformBornVertex_incidence_upper (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ birth age (vertex : XiVtx system birth),
      xiVertexBornAt system birth vertex →
      (xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) ≤
        coefficient * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age := by
  obtain ⟨globalConstant, globalPositive, globalBound⟩ :=
    exists_xiUniformVertex_incidence_bound system connected primitiveDegree
  obtain ⟨recentConstant, recentPositive, recentBound⟩ :=
    exists_xiRecentVertex_incidence_bound system primitiveDegree
  obtain ⟨growthConstant, growthPositive, growthBound⟩ :=
    exists_uniform_xiIncidence_growth_upper system primitiveDegree
  have degreePositive := zero_lt_one.trans (degree_spectralRadius_gt_one_of_primitive system primitiveDegree)
  let birthConstant := globalConstant + recentConstant * finiteRealMatrixSpectralRadius (degreeMatrix system)
  have birthPositive : 0 < birthConstant := by dsimp [birthConstant]; positivity
  have birthBound : ∀ birth (vertex : XiVtx system birth), xiVertexBornAt system birth vertex →
      (xiVertexIncidenceCount system birth vertex : ℝ) ≤ birthConstant := by
    intro birth vertex born
    cases birth with
    | zero =>
      have actual := globalBound 0 vertex
      simp only [pow_zero, mul_one] at actual
      exact actual.trans (by dsimp [birthConstant]; linarith [mul_pos recentPositive degreePositive])
    | succ birth =>
      have actual := recentBound birth 1 vertex born
      simp only [pow_one] at actual
      exact actual.trans (by dsimp [birthConstant]; linarith)
  refine ⟨growthConstant * birthConstant, mul_pos growthPositive birthPositive, ?_⟩
  intro birth age vertex born
  exact (growthBound birth age vertex).trans
    ((mul_le_mul_of_nonneg_left (birthBound birth vertex born)
      (mul_nonneg growthPositive.le (pow_nonneg degreePositive.le age))).trans_eq (by ring))

theorem exists_xiUniformVertex_incidence_lower (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ birth age (vertex : XiVtx system birth),
      coefficient * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age ≤
        (xiVertexIncidenceCount system (birth + age) (xiForward system birth age vertex) : ℝ) := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  obtain ⟨weights, weightsPositive, ratePositive, normalized, eigenpair⟩ :=
    primitive_matrix_spectralRadius_eigenpair_finite (degreeMatrix system) primitiveDegree
  obtain ⟨minimumState, _, minimumBound⟩ := Finset.univ.exists_min_image weights Finset.univ_nonempty
  have weightedAtMost (level : ℕ) (vertex : XiVtx system level) :
      (∑ state, degVec system level vertex state * weights state) ≤
        (xiVertexIncidenceCount system level vertex : ℝ) := by
    rw [xiVertexIncidenceCount_eq_degree_state_sum]
    apply Finset.sum_le_sum
    intro state _
    have nonnegative : 0 ≤ degVec system level vertex state := by cases state <;> exact Nat.cast_nonneg _
    have atMostOne : weights state ≤ 1 := by
      rw [← normalized]
      exact Finset.single_le_sum (fun other _ => (weightsPositive other).le) (Finset.mem_univ _)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left atMostOne nonnegative
  refine ⟨weights minimumState, weightsPositive _, ?_⟩
  intro birth age vertex
  have incidencePositive : 0 < (xiVertexIncidenceCount system birth vertex : ℝ) := by
    rw [xiVertexIncidenceCount_eq_degree_state_sum]
    simpa only [mul_one] using degVec_weighted_positive system connected birth vertex (fun _ => 1) (fun _ => by norm_num)
  have incidenceOne : (1 : ℝ) ≤ (xiVertexIncidenceCount system birth vertex : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.cast_pos.mp incidencePositive)))
  have initialMinimum : weights minimumState ≤ ∑ state, degVec system birth vertex state * weights state := by
    calc
      _ ≤ weights minimumState * (xiVertexIncidenceCount system birth vertex : ℝ) := by nlinarith [weightsPositive minimumState]
      _ ≤ _ := by
        rw [xiVertexIncidenceCount_eq_degree_state_sum, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro state _
        have nonnegative : 0 ≤ degVec system birth vertex state := by cases state <;> exact Nat.cast_nonneg _
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (minimumBound state (Finset.mem_univ _)) nonnegative
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
  calc
    _ ≤ (∑ state, degVec system birth vertex state * weights state) *
        finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age :=
      mul_le_mul_of_nonneg_right initialMinimum (pow_nonneg ratePositive.le age)
    _ = _ := (weightedIdentity age).symm
    _ ≤ _ := weightedAtMost _ _

theorem exists_xiUniformBornVertex_geometric_ball_mass (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system) (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    ∃ lower upper lowerRadius upperRadius : ℝ,
      0 < lower ∧ 0 < upper ∧ 0 < lowerRadius ∧ 0 < upperRadius ∧
      ∀ birth age (vertex : XiVtx system birth), xiVertexBornAt system birth vertex →
        lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age / mass.rate ^ (birth + age) ≤
          (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
            (Metric.ball (xiCompletionEmbedding system connected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair birth vertex) (lowerRadius * rate⁻¹ ^ (birth + age))) ∧
        (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
            (Metric.closedBall (xiCompletionEmbedding system connected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair birth vertex) (upperRadius * rate⁻¹ ^ (birth + age))) ≤
          upper * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age / mass.rate ^ (birth + age) := by
  obtain ⟨starLower, lowerRadius, starLowerPositive, lowerRadiusPositive, lowerBound⟩ :=
    exists_xiVertexStarBallMassLower system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
  obtain ⟨lowerLength, lowerPositive, lengthLower⟩ := exists_positive_colour_length_lower_bound system lengths lengthsPositive
  obtain ⟨starUpper, starUpperPositive, upperBound⟩ := exists_xiVertexClosedBall_incidence_mass_upper system connected
    lengths lengthsPositive rate rateGreaterThanOne eigenpair mass lowerLength lowerPositive lengthLower
  obtain ⟨degreeLower, degreeLowerPositive, degreeLowerBound⟩ := exists_xiUniformVertex_incidence_lower system connected primitiveDegree
  obtain ⟨degreeUpper, degreeUpperPositive, degreeUpperBound⟩ := exists_xiUniformBornVertex_incidence_upper system connected primitiveDegree
  refine ⟨starLower * degreeLower, starUpper * degreeUpper, lowerRadius, lowerLength / 2,
    mul_pos starLowerPositive degreeLowerPositive, mul_pos starUpperPositive degreeUpperPositive,
    lowerRadiusPositive, by positivity, ?_⟩
  intro birth age vertex born
  have actualLower := lowerBound (birth + age) (xiForward system birth age vertex)
  have actualUpper := upperBound (birth + age) (xiForward system birth age vertex)
    (lowerLength / 2 * rate⁻¹ ^ (birth + age)) (by
      have positive := pow_pos (inv_pos.mpr (zero_lt_one.trans rateGreaterThanOne)) (birth + age)
      nlinarith)
  rw [xiCompletionEmbedding_forward] at actualLower actualUpper
  constructor
  · calc
      _ = starLower / mass.rate ^ (birth + age) *
          (degreeLower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left (degreeLowerBound birth age vertex)
        (div_pos starLowerPositive (pow_pos mass.rate_positive _)).le).trans actualLower
  · exact actualUpper.trans ((mul_le_mul_of_nonneg_left (degreeUpperBound birth age vertex born)
      (div_pos starUpperPositive (pow_pos mass.rate_positive _)).le).trans_eq (by ring))

end
end EIGS
#print axioms EIGS.exists_xiUniformBornVertex_incidence_upper
#print axioms EIGS.exists_xiUniformVertex_incidence_lower
#print axioms EIGS.exists_xiUniformBornVertex_geometric_ball_mass



namespace EIGS
open MeasureTheory Metric
open scoped Classical
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiUniformBirthFactor_ball_mass_at_fixed_radius (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system) (primitiveDegree : (degreeMatrix system).IsPrimitive)
    (radiusFactor : ℝ) (radiusFactorPositive : 0 < radiusFactor) :
    ∃ lower upper : ℝ, ∃ minimumAge : ℕ, 0 < lower ∧ 0 < upper ∧
      ∀ birth age (vertex : XiVtx system birth), minimumAge ≤ age → xiVertexBornAt system birth vertex →
        lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age / mass.rate ^ (birth + age) ≤
          (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
            (Metric.ball (xiCompletionEmbedding system connected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair birth vertex) (radiusFactor * rate⁻¹ ^ (birth + age))) ∧
        (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
            (Metric.closedBall (xiCompletionEmbedding system connected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair birth vertex) (radiusFactor * rate⁻¹ ^ (birth + age))) ≤
          upper * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age / mass.rate ^ (birth + age) := by
  obtain ⟨lower, upper, lowerRadius, upperRadius, lowerPositive, upperPositive,
    lowerRadiusPositive, upperRadiusPositive, bounds⟩ := exists_xiUniformBornVertex_geometric_ball_mass system
      connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass primitiveDegree
  have ratePositive := zero_lt_one.trans rateGreaterThanOne
  have invSmall := (inv_lt_one₀ ratePositive).mpr rateGreaterThanOne
  have degreePositive := zero_lt_one.trans (degree_spectralRadius_gt_one_of_primitive system primitiveDegree)
  have massPositive := mass.rate_positive
  obtain ⟨lowerShift, lowerSmall⟩ := exists_pow_lt_of_lt_one (div_pos radiusFactorPositive lowerRadiusPositive) invSmall
  obtain ⟨upperShift, upperSmall⟩ := exists_pow_lt_of_lt_one (div_pos upperRadiusPositive radiusFactorPositive) invSmall
  have lowerFit : lowerRadius * rate⁻¹ ^ lowerShift < radiusFactor := by
    simpa only [mul_comm] using (lt_div_iff₀ lowerRadiusPositive).mp lowerSmall
  have upperFit : radiusFactor * rate⁻¹ ^ upperShift < upperRadius := by
    simpa only [mul_comm] using (lt_div_iff₀ radiusFactorPositive).mp upperSmall
  refine ⟨lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ lowerShift / mass.rate ^ lowerShift,
    upper * mass.rate ^ upperShift / finiteRealMatrixSpectralRadius (degreeMatrix system) ^ upperShift,
    upperShift, by positivity, by positivity, ?_⟩
  intro birth age vertex ageLarge born
  have low := (bounds birth (age + lowerShift) vertex born).1
  have high := (bounds birth (age - upperShift) vertex born).2
  have lowerRadiusLe : lowerRadius * rate⁻¹ ^ (birth + (age + lowerShift)) ≤
      radiusFactor * rate⁻¹ ^ (birth + age) := by
    rw [show birth + (age + lowerShift) = (birth + age) + lowerShift by omega, pow_add]
    have scaled := mul_lt_mul_of_pos_right lowerFit (pow_pos (inv_pos.mpr ratePositive) (birth + age))
    nlinarith only [scaled]
  have upperRadiusLe : radiusFactor * rate⁻¹ ^ (birth + age) ≤
      upperRadius * rate⁻¹ ^ (birth + (age - upperShift)) := by
    rw [show birth + age = (birth + (age - upperShift)) + upperShift by omega, pow_add]
    have scaled := mul_lt_mul_of_pos_right upperFit (pow_pos (inv_pos.mpr ratePositive) (birth + (age - upperShift)))
    nlinarith only [scaled]
  have lowerAlgebra :
      (lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ lowerShift / mass.rate ^ lowerShift) *
        finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age / mass.rate ^ (birth + age) =
      lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ (age + lowerShift) /
        mass.rate ^ (birth + (age + lowerShift)) := by
    rw [show birth + (age + lowerShift) = (birth + age) + lowerShift by omega, pow_add, pow_add]
    field_simp [mass.rate_positive.ne', degreePositive.ne']
    <;> ring
  have upperAlgebra : upper * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ (age - upperShift) /
        mass.rate ^ (birth + (age - upperShift)) =
      (upper * mass.rate ^ upperShift / finiteRealMatrixSpectralRadius (degreeMatrix system) ^ upperShift) *
        finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age / mass.rate ^ (birth + age) := by
    have degreePower : finiteRealMatrixSpectralRadius (degreeMatrix system) ^ age =
        finiteRealMatrixSpectralRadius (degreeMatrix system) ^ (age - upperShift) *
          finiteRealMatrixSpectralRadius (degreeMatrix system) ^ upperShift := by
      rw [← pow_add, Nat.sub_add_cancel ageLarge]
    have massPower : mass.rate ^ (birth + age) = mass.rate ^ (birth + (age - upperShift)) * mass.rate ^ upperShift := by
      rw [← pow_add]
      congr 1
      omega
    rw [degreePower, massPower]
    field_simp [mass.rate_positive.ne', degreePositive.ne']
    <;> ring
  constructor
  · rw [lowerAlgebra]
    exact low.trans (measureReal_mono (Metric.ball_subset_ball lowerRadiusLe))
  · exact (measureReal_mono (Metric.closedBall_subset_closedBall upperRadiusLe)).trans (high.trans_eq upperAlgebra)

end
end EIGS
#print axioms EIGS.exists_xiUniformBirthFactor_ball_mass_at_fixed_radius



namespace EIGS
open MeasureTheory Filter Topology Metric
open scoped Classical ENNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def xiPhysicalSkeletonCollar (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (coarse : ℕ) (radius : ℝ) :
    Set (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
  {point | infDist point (Set.range (xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse)) ≤ radius}

theorem xiPhysicalSkeletonCollar_pullback_subset (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (lowerLength : ℝ) (lowerLengthPositive : 0 < lowerLength)
    (lengthLower : ∀ colour, lowerLength ≤ lengths colour)
    (coarse width : ℕ) (radius : ℝ) (radiusSmall : radius < lowerLength * rate⁻¹ ^ (coarse + width)) :
    (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) ⁻¹'
      xiPhysicalSkeletonCollar system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair coarse radius ⊆
        xiAddressEndpointCollar system coarse width := by
  intro address inside
  let embedding := xiCompletionEmbedding system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse
  have compact : IsCompact (Set.range embedding) := (Set.finite_range embedding).isCompact
  have nonempty : (Set.range embedding).Nonempty := ⟨embedding (xiPositiveTerminal system coarse), Set.mem_range_self _⟩
  obtain ⟨point, ⟨vertex, rfl⟩, distanceEquality⟩ := compact.exists_infDist_eq_dist nonempty
    (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair address)
  have near : dist (embedding vertex)
      (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair address) ≤ radius := by
    change infDist _ (Set.range embedding) ≤ radius at inside
    simpa only [distanceEquality, dist_comm] using inside
  have incidence : XiTail system (coarse + width) (xiAddressEdge system (coarse + width) address) =
      xiForward system coarse width vertex ∨
      XiHead system (coarse + width) (xiAddressEdge system (coarse + width) address) =
      xiForward system coarse width vertex := by
    by_contra neither
    have separated := xiAddressLimit_vertex_separated_of_nonincident system connected lengths lengthsPositive
      rate rateGreaterThanOne eigenpair lowerLength lowerLengthPositive lengthLower (coarse + width)
      (xiForward system coarse width vertex) address (not_or.mp neither).1 (not_or.mp neither).2
    rw [xiCompletionEmbedding_forward] at separated
    exact (not_lt_of_ge separated) (near.trans_lt radiusSmall)
  refine ⟨vertex, ?_⟩
  rcases incidence with incidence | incidence <;>
    unfold xiAddressStarWeight xiEdgeStarMultiplicity <;>
    simp only [incidence, if_true] <;> split_ifs <;> norm_num

theorem exists_xiPhysicalSkeletonCollar_geometric_mass_bound (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system) (primitiveDegree : (degreeMatrix system).IsPrimitive)
    (radiusFactor : ℝ) (radiusFactorPositive : 0 < radiusFactor) :
    ∃ coefficient : ℝ, ∃ minimumWidth : ℕ, 0 < coefficient ∧ ∀ level width : ℕ,
      minimumWidth ≤ width → width ≤ level →
      (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
        (xiPhysicalSkeletonCollar system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
          (level - width) (radiusFactor * rate⁻¹ ^ level)) ≤
      ENNReal.ofReal (coefficient * (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) ^ width) := by
  obtain ⟨lowerLength, lowerPositive, lowerBound⟩ := exists_positive_colour_length_lower_bound system lengths lengthsPositive
  obtain ⟨constant, constantPositive, bound⟩ := exists_xiAddressEndpointCollar_mass_bound system mass primitiveDegree
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  obtain ⟨_, _, degreePositive, _, _⟩ :=
    primitive_matrix_spectralRadius_eigenpair_finite (degreeMatrix system) primitiveDegree
  have ratioPositive := div_pos degreePositive mass.rate_positive
  obtain ⟨shift, shiftSmall⟩ := exists_pow_lt_of_lt_one
    (div_pos lowerPositive radiusFactorPositive)
    ((inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne)
  have shiftedSmall : radiusFactor * rate⁻¹ ^ shift < lowerLength :=
    by simpa only [mul_comm] using (lt_div_iff₀ radiusFactorPositive).mp shiftSmall
  refine ⟨constant / (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) ^ shift,
    shift, div_pos constantPositive (pow_pos ratioPositive _), ?_⟩
  intro level width shiftLe widthLe
  have indexEquality : (level - width) + (width - shift) + shift = level := by omega
  have radiusSmall : radiusFactor * rate⁻¹ ^ level <
      lowerLength * rate⁻¹ ^ ((level - width) + (width - shift)) := by
    have powerEquality : rate⁻¹ ^ level = rate⁻¹ ^ ((level - width) + (width - shift)) * rate⁻¹ ^ shift := by
      rw [← pow_add, indexEquality]
    rw [powerEquality]
    have scaled := mul_lt_mul_of_pos_right shiftedSmall
      (pow_pos (inv_pos.mpr (zero_lt_one.trans rateGreaterThanOne)) ((level - width) + (width - shift)))
    nlinarith only [scaled]
  have inclusion := xiPhysicalSkeletonCollar_pullback_subset system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair lowerLength lowerPositive lowerBound (level - width) (width - shift)
    (radiusFactor * rate⁻¹ ^ level) radiusSmall
  have measurable : MeasurableSet (xiPhysicalSkeletonCollar system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair (level - width) (radiusFactor * rate⁻¹ ^ level)) :=
    measurableSet_le (continuous_infDist_pt _).measurable measurable_const
  rw [xiLimitMeasure, Measure.map_apply
    (measurable_xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) measurable]
  have algebra : constant * (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) ^ (width - shift) =
      (constant / (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) ^ shift) *
        (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) ^ width := by
    have powers : (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) ^ width =
        (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) ^ (width - shift) *
          (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) ^ shift := by
      rw [← pow_add, Nat.sub_add_cancel shiftLe]
    rw [powers]
    field_simp [ratioPositive.ne']
    <;> ring
  exact (measure_mono inclusion).trans ((bound (level - width) (width - shift)).trans_eq (by rw [algebra]))

end
end EIGS
#print axioms EIGS.xiPhysicalSkeletonCollar_pullback_subset
#print axioms EIGS.exists_xiPhysicalSkeletonCollar_geometric_mass_bound






namespace EIGS
open MeasureTheory
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem exists_xiPhysicalSkeletonCollar_geometric_real_mass_bound (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system) (primitiveDegree : (degreeMatrix system).IsPrimitive)
    (radiusFactor : ℝ) (radiusFactorPositive : 0 < radiusFactor) :
    ∃ coefficient : ℝ, ∃ minimumWidth : ℕ, 0 < coefficient ∧ ∀ level width : ℕ,
      minimumWidth ≤ width → width ≤ level →
      (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).real
        (xiPhysicalSkeletonCollar system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
          (level - width) (radiusFactor * rate⁻¹ ^ level)) ≤
      coefficient * (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) ^ width := by
  obtain ⟨coefficient, minimumWidth, coefficientPositive, bound⟩ :=
    exists_xiPhysicalSkeletonCollar_geometric_mass_bound system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass primitiveDegree radiusFactor radiusFactorPositive
  have degreePositive := zero_lt_one.trans (degree_spectralRadius_gt_one_of_primitive system primitiveDegree)
  have massPositive := mass.rate_positive
  refine ⟨coefficient, minimumWidth, coefficientPositive, ?_⟩
  intro level width widthLarge widthLe
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (bound level width widthLarge widthLe)

end
end EIGS
#print axioms EIGS.exists_xiPhysicalSkeletonCollar_geometric_real_mass_bound



namespace EIGS.MeasuredGHP
open Metric Set
noncomputable section

theorem diameterNormalized_finiteSkeletonCollar_eq_native (Space : Type) [original : MetricSpace Space]
    (diameterPositive : 0 < Metric.diam (univ : Set Space)) {Vertex : Type} [Fintype Vertex] [Nonempty Vertex]
    (embedding : Vertex → Space) (radius : ℝ) :
    {point | @Metric.infDist Space (normalizedMetric Space original diameterPositive).toPseudoMetricSpace
      point (Set.range embedding) ≤ radius} =
    {point | Metric.infDist point (Set.range embedding) ≤ Metric.diam (univ : Set Space) * radius} := by
  ext point
  have attained (metric : MetricSpace Space) : ∃ vertex : Vertex,
      @Metric.infDist Space metric.toPseudoMetricSpace point (Set.range embedding) =
        @dist Space metric.toDist point (embedding vertex) := by
    letI := metric
    obtain ⟨other, ⟨vertex, rfl⟩, equality⟩ :=
      (Set.finite_range embedding).isCompact.exists_infDist_eq_dist
        (Set.range_nonempty embedding) point
    exact ⟨vertex, equality⟩
  constructor
  · intro inside
    obtain ⟨vertex, equality⟩ := attained (normalizedMetric Space original diameterPositive)
    change @Metric.infDist Space (normalizedMetric Space original diameterPositive).toPseudoMetricSpace
      point (Set.range embedding) ≤ radius at inside
    rw [equality, diameterNormalized_dist_exact] at inside
    exact (Metric.infDist_le_dist_of_mem (Set.mem_range_self vertex)).trans (by
      simpa only [mul_comm] using (div_le_iff₀ diameterPositive).mp inside)
  · intro inside
    obtain ⟨vertex, equality⟩ := attained original
    change Metric.infDist point (Set.range embedding) ≤ Metric.diam (univ : Set Space) * radius at inside
    rw [equality] at inside
    have close : @dist Space (normalizedMetric Space original diameterPositive).toDist point (embedding vertex) ≤ radius := by
      rw [diameterNormalized_dist_exact]
      exact (div_le_iff₀ diameterPositive).mpr (by simpa only [mul_comm] using inside)
    have minimum : @Metric.infDist Space (normalizedMetric Space original diameterPositive).toPseudoMetricSpace
        point (Set.range embedding) ≤
        @dist Space (normalizedMetric Space original diameterPositive).toDist point (embedding vertex) := by
      letI := normalizedMetric Space original diameterPositive
      exact Metric.infDist_le_dist_of_mem (Set.mem_range_self vertex)
    exact minimum.trans close

end
end EIGS.MeasuredGHP

namespace EIGS
open MeasureTheory Metric
open scoped Classical
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiUniformBirthFactorAndSpatialCollar_diameter_of_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive)
    (radiusFactor : ℝ) (radiusFactorPositive : 0 < radiusFactor) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
    let normalizedMetric := MeasuredGHP.xiCompletionDiameterMetricSpace system connected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
    ∃ lower upper collar : ℝ, ∃ minimumAge minimumWidth : ℕ,
      0 < lower ∧ 0 < upper ∧ 0 < collar ∧
      (∀ birth level (vertex : XiVtx system birth), birth + minimumAge ≤ level → xiVertexBornAt system birth vertex →
        lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ (level - birth) / mass.rate ^ level ≤
          (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
            (@Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace
              (parameters.vertexEmbedding birth vertex) (radiusFactor * (system.distanceSpectralRadius connected)⁻¹ ^ level)) ∧
        (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
            (@Metric.closedBall parameters.LimitSpace normalizedMetric.toPseudoMetricSpace
              (parameters.vertexEmbedding birth vertex) (radiusFactor * (system.distanceSpectralRadius connected)⁻¹ ^ level)) ≤
          upper * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ (level - birth) / mass.rate ^ level) ∧
      ∀ level width : ℕ, minimumWidth ≤ width → width ≤ level →
        (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
          {point | @Metric.infDist parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point
            (Set.range (parameters.vertexEmbedding (level - width))) ≤
              radiusFactor * (system.distanceSpectralRadius connected)⁻¹ ^ level} ≤
          collar * (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) ^ width := by
  intro parameters distanceGreaterThanOne mass normalizedMetric
  let diameter := xiCompletionDiameter system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair
  have diameterPositive : 0 < diameter := xiCompletionDiameter_positive system connected parameters.lengths
    parameters.lengthsPositive (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
  let nativeMetric : MetricSpace parameters.LimitSpace := xiCompletionMetricSpace system connected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
    (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair
  have ballIdentity (point : parameters.LimitSpace) (radius : ℝ) :
      @Metric.ball parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius =
        @Metric.ball parameters.LimitSpace nativeMetric.toPseudoMetricSpace point (diameter * radius) :=
    @MeasuredGHP.diameterNormalized_ball_eq_native parameters.LimitSpace nativeMetric diameterPositive point radius
  have closedBallIdentity (point : parameters.LimitSpace) (radius : ℝ) :
      @Metric.closedBall parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point radius =
        @Metric.closedBall parameters.LimitSpace nativeMetric.toPseudoMetricSpace point (diameter * radius) := by
    ext other
    change diameter⁻¹ * dist other point ≤ radius ↔ dist other point ≤ diameter * radius
    rw [mul_comm diameter⁻¹, ← div_eq_mul_inv, div_le_iff₀ diameterPositive, mul_comm radius]
  have collarIdentity (coarse : ℕ) (radius : ℝ) :
      {point | @Metric.infDist parameters.LimitSpace normalizedMetric.toPseudoMetricSpace point
        (Set.range (parameters.vertexEmbedding coarse)) ≤ radius} =
      {point | @Metric.infDist parameters.LimitSpace nativeMetric.toPseudoMetricSpace point
        (Set.range (parameters.vertexEmbedding coarse)) ≤ diameter * radius} :=
    @MeasuredGHP.diameterNormalized_finiteSkeletonCollar_eq_native parameters.LimitSpace nativeMetric
      diameterPositive (XiVtx system coarse) inferInstance inferInstance (parameters.vertexEmbedding coarse) radius
  obtain ⟨lower, upper, minimumAge, lowerPositive, upperPositive, volumeBound⟩ :=
    exists_xiUniformBirthFactor_ball_mass_at_fixed_radius system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass primitiveDegree
      (diameter * radiusFactor) (mul_pos diameterPositive radiusFactorPositive)
  obtain ⟨collar, minimumWidth, collarPositive, collarBound⟩ :=
    exists_xiPhysicalSkeletonCollar_geometric_real_mass_bound system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass primitiveDegree
      (diameter * radiusFactor) (mul_pos diameterPositive radiusFactorPositive)
  refine ⟨lower, upper, collar, minimumAge, minimumWidth, lowerPositive, upperPositive, collarPositive, ?_, ?_⟩
  · intro birth level vertex levelLarge born
    have birthLe : birth ≤ level := by omega
    have ageLarge : minimumAge ≤ level - birth := by omega
    rw [ballIdentity, closedBallIdentity]
    simpa only [mul_assoc, Nat.add_sub_of_le birthLe] using
      volumeBound birth (level - birth) vertex ageLarge born
  · intro level width widthLarge widthLe
    have equality := congrArg
      (fun region : Set parameters.LimitSpace =>
        (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real region)
      (collarIdentity (level - width) (radiusFactor * (system.distanceSpectralRadius connected)⁻¹ ^ level))
    exact equality.le.trans (by
      simpa only [xiPhysicalSkeletonCollar, mul_assoc] using collarBound level width widthLarge widthLe)

end
end EIGS
#print axioms EIGS.MeasuredGHP.diameterNormalized_finiteSkeletonCollar_eq_native
#print axioms EIGS.exists_xiUniformBirthFactorAndSpatialCollar_diameter_of_rules





