import RequestProject.Section31.EIGSStationaryDegreePointCountBounds
import RequestProject.Section31.FiniteGeometricLadderSupportLimit
import RequestProject.Section2ScaleLimits
import RequestProject.Section2PrimitiveIntegerGrowth
import Mathlib.Topology.Order.LiminfLimsup

/-! Original stationary degree dimension, Li--Britz arXiv:2109.14463v2
Definitions 3.1--3.2, on the actual EIGS vertex union. The full occupied
point-count support is used. All geometric birth counts and maximum-degree
limits are derived from the rules. No cited scale-free theorem is assumed.
The final rule-only theorem fills nu>1 internally from the actual primitive
integer degree matrix. Candidate source. -/

namespace EIGS
open Filter Topology
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

def xiStationaryOccupiedDegreeSupport (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (coefficient rate normalizer : ℝ) : Set ℝ :=
  {value | 0 < value ∧ 0 < xiStationaryDegreeMultiplicity system weights coefficient rate normalizer value}

theorem xiStationaryDegree_ladder_logarithmic_limit (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (weights : Fin K ⊕ Fin K → ℝ) (weightsPositive : ∀ state, 0 < weights state)
    (coefficient rate normalizer : ℝ) (coefficientPositive : 0 < coefficient)
    (rateGreaterThanOne : 1 < rate) (normalizerPositive : 0 < normalizer)
    (mass : XiMassParameters system) (kind : XiPrivateBirthType system) :
    Tendsto (fun level : ℕ =>
      Real.log (xiStationaryDegreeMultiplicity system weights coefficient rate normalizer
        (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind / rate ^ level) : ℝ) /
      (-Real.log (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind / rate ^ level)))
      atTop (𝓝 (Real.log mass.rate / Real.log rate)) := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, countBounds⟩ :=
    xiStationaryDegree_point_count_bounds system connected plantingNonadjacent distancePositive
      weights weightsPositive coefficient rate normalizer coefficientPositive rateGreaterThanOne normalizerPositive mass
  have coefficientPositive := xiPrivateDegreeLadderCoefficient_positive system connected distancePositive
    weights weightsPositive coefficient rate normalizer coefficientPositive
    (zero_lt_one.trans rateGreaterThanOne) normalizerPositive kind
  have inverseIdentity (level : ℕ) :
      (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind / rate ^ level)⁻¹ =
        (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind)⁻¹ * rate ^ level := by
    rw [inv_div, div_eq_mul_inv, mul_comm]
  have radiusGrowth : Tendsto (fun level : ℕ =>
      (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind / rate ^ level)⁻¹)
      atTop atTop := by
    simp only [inverseIdentity]
    exact Tendsto.const_mul_atTop (inv_pos.2 coefficientPositive)
      (tendsto_pow_atTop_atTop_of_one_lt rateGreaterThanOne)
  have actual := logarithmic_ratio_limit_of_geometric_scale
    (sequence := fun level : ℕ => (xiStationaryDegreeMultiplicity system weights coefficient rate normalizer
      (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind / rate ^ level) : ℝ))
    (radius := fun level : ℕ =>
      (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind / rate ^ level)⁻¹)
    (depth := fun level : ℕ => level) (rate := mass.rate) (distance_rate := rate)
    (lower := lower) (upper := upper)
    (radius_lower := (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind)⁻¹)
    (radius_upper := (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind)⁻¹)
    mass.rate_positive rateGreaterThanOne lowerPositive upperPositive
    (inv_pos.2 coefficientPositive) (inv_pos.2 coefficientPositive) radiusGrowth
    ((eventually_ge_atTop 1).mono (fun level large => countBounds kind level large))
    (Eventually.of_forall (fun level => by
      change (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind)⁻¹ * rate ^ level ≤
          (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind / rate ^ level)⁻¹ ∧
        (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind / rate ^ level)⁻¹ ≤
          (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind)⁻¹ * rate ^ level
      rw [inverseIdentity]
      exact ⟨le_rfl, le_rfl⟩))
  simpa only [Real.log_inv] using actual

theorem xiStationaryDegree_full_support_logarithmic_limit (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (weights : Fin K ⊕ Fin K → ℝ) (weightsPositive : ∀ state, 0 < weights state)
    (coefficient rate normalizer : ℝ) (coefficientPositive : 0 < coefficient)
    (rateGreaterThanOne : 1 < rate) (normalizerPositive : 0 < normalizer)
    (mass : XiMassParameters system) :
    Tendsto (fun value : ℝ =>
      Real.log (xiStationaryDegreeMultiplicity system weights coefficient rate normalizer value : ℝ) / (-Real.log value))
      (𝓝[xiStationaryOccupiedDegreeSupport system weights coefficient rate normalizer] (0 : ℝ))
      (𝓝 (Real.log mass.rate / Real.log rate)) ∧
    NeBot (𝓝[xiStationaryOccupiedDegreeSupport system weights coefficient rate normalizer] (0 : ℝ)) := by
  letI : Nonempty (XiPrivateBirthType system) := xiPrivateBirthType_nonempty system connected plantingNonadjacent
  have coefficientsPositive := xiPrivateDegreeLadderCoefficient_positive system connected distancePositive
    weights weightsPositive coefficient rate normalizer coefficientPositive
    (zero_lt_one.trans rateGreaterThanOne) normalizerPositive
  have initialPositive : ∀ vertex : Bool, 0 <
      xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer (Sum.inl vertex) := by
    intro vertex
    unfold xiStationaryDegreeFromAmplitudes
    rw [xiDegreeLimitAmplitude_initial]
    cases vertex <;> exact div_pos (mul_pos coefficientPositive (weightsPositive _)) normalizerPositive
  have supportContained : xiStationaryOccupiedDegreeSupport system weights coefficient rate normalizer ⊆
      Set.range (fun vertex : Bool => xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer
        (Sum.inl vertex)) ∪
      Set.range (fun code : XiPrivateBirthType system × ℕ =>
        xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer code.1 / rate ^ code.2) := by
    intro value occupied
    letI : Finite {vertex : XiVertexUnion system //
        xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer vertex = value} :=
      xiStationaryDegree_fiber_finite system connected distancePositive weights weightsPositive
        coefficient rate normalizer coefficientPositive rateGreaterThanOne normalizerPositive value
    obtain ⟨vertex⟩ := Finite.card_pos_iff.mp occupied.2
    obtain ⟨vertex, sameValue⟩ := vertex
    cases vertex with
    | inl initial => exact Or.inl ⟨initial, sameValue⟩
    | inr privateBirth =>
      obtain ⟨level, privateVertex⟩ := privateBirth
      exact Or.inr ⟨(xiPrivateBirthTypeOf system level privateVertex, level),
        (xiStationaryDegree_private_birth_formula system weights coefficient rate normalizer level privateVertex).symm.trans sameValue⟩
  constructor
  · exact finite_geometric_ladder_support_limit
      (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer) coefficientsPositive
      (fun vertex : Bool => xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer (Sum.inl vertex))
      initialPositive rate rateGreaterThanOne
      (xiStationaryOccupiedDegreeSupport system weights coefficient rate normalizer) supportContained
      (fun value : ℝ => Real.log (xiStationaryDegreeMultiplicity system weights coefficient rate normalizer value : ℝ) /
        (-Real.log value)) (Real.log mass.rate / Real.log rate)
      (xiStationaryDegree_ladder_logarithmic_limit system connected plantingNonadjacent distancePositive
        weights weightsPositive coefficient rate normalizer coefficientPositive rateGreaterThanOne normalizerPositive mass)
  · obtain ⟨kind⟩ := ‹Nonempty (XiPrivateBirthType system)›
    apply geometric_ladder_occupied_support_accumulates
      (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind) rate
      (coefficientsPositive kind) rateGreaterThanOne
    intro level
    obtain ⟨lower, upper, lowerPositive, upperPositive, countBounds⟩ :=
      xiStationaryDegree_point_count_bounds system connected plantingNonadjacent distancePositive
        weights weightsPositive coefficient rate normalizer coefficientPositive rateGreaterThanOne normalizerPositive mass
    refine ⟨div_pos (coefficientsPositive kind) (pow_pos (zero_lt_one.trans rateGreaterThanOne) _), ?_⟩
    have realPositive := (mul_pos lowerPositive (pow_pos mass.rate_positive (level + 1))).trans_le
      (countBounds kind (level + 1) (by omega)).1
    exact_mod_cast realPositive

theorem primitive_rules_original_degree_dimension (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitive : (degreeMatrix system).IsPrimitive) :
    ∃ weights : Fin K ⊕ Fin K → ℝ, ∃ coefficient normalizer : ℝ,
      (∀ vertex, 0 < xiStationaryDegreeFromAmplitudes system weights coefficient
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer vertex ∧
        xiStationaryDegreeFromAmplitudes system weights coefficient
          (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer vertex ≤ 1) ∧
      (∀ vertex, Tendsto (fun level => xiActualMaxNormalizedDegree system level vertex) atTop
        (𝓝 (xiStationaryDegreeFromAmplitudes system weights coefficient
          (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer vertex))) ∧
      (∀ value : ℝ, Finite {vertex : XiVertexUnion system //
        xiStationaryDegreeFromAmplitudes system weights coefficient
          (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer vertex = value}) ∧
      0 < Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData)) /
        Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) ∧
      Tendsto (fun value : ℝ => Real.log (xiStationaryDegreeMultiplicity system weights coefficient
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer value : ℝ) / (-Real.log value))
        (𝓝[xiStationaryOccupiedDegreeSupport system weights coefficient
          (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer] (0 : ℝ))
        (𝓝 (Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData)) /
          Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)))) ∧
      NeBot (𝓝[xiStationaryOccupiedDegreeSupport system weights coefficient
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer] (0 : ℝ)) ∧
      Filter.limsup (fun value : ℝ => Real.log (xiStationaryDegreeMultiplicity system weights coefficient
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer value : ℝ) / (-Real.log value))
        (𝓝[xiStationaryOccupiedDegreeSupport system weights coefficient
          (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer] (0 : ℝ)) =
        Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData)) /
          Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) := by
  have degreeSupercritical := degree_spectralRadius_gt_one_of_primitive system primitive
  obtain ⟨weights, coefficient, normalizer, weightsPositive, normalized, eigenpair,
    coefficientPositive, normalizerPositive, stationaryBounds, stationaryConvergence⟩ :=
      primitive_rules_explicit_stationary_degree system connected loopless unique plantingNonadjacent
        primitive degreeSupercritical
  let mass := xiMassParametersOfRules system connected distancePositive
  obtain ⟨distributionLimit, supportAccumulates⟩ := xiStationaryDegree_full_support_logarithmic_limit system
    connected plantingNonadjacent distancePositive weights weightsPositive coefficient
      (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer coefficientPositive
        degreeSupercritical normalizerPositive mass
  have rateEquality := XiMassParameters.rate_eq_spectralRadius system mass
  rw [rateEquality] at distributionLimit
  have dimensionPositive : 0 < Real.log (realMatrixSpectralRadius (massMatrixR system.toRuleData)) /
      Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) := by
    apply div_pos
    · rw [← rateEquality]
      exact Real.log_pos ((by norm_num : (1 : ℝ) < 2).trans_le
        (XiMassParameters.rate_ge_two system connected plantingNonadjacent mass))
    · exact Real.log_pos degreeSupercritical
  letI := supportAccumulates
  exact ⟨weights, coefficient, normalizer, stationaryBounds, stationaryConvergence,
    xiStationaryDegree_fiber_finite system connected distancePositive weights weightsPositive
      coefficient (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer coefficientPositive
        degreeSupercritical normalizerPositive,
    dimensionPositive, distributionLimit, supportAccumulates, distributionLimit.limsup_eq⟩

end
end EIGS

#print axioms EIGS.xiStationaryDegree_ladder_logarithmic_limit
#print axioms EIGS.xiStationaryDegree_full_support_logarithmic_limit
#print axioms EIGS.primitive_rules_original_degree_dimension
