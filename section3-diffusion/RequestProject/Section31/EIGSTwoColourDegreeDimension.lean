import RequestProject.Section31.EIGSTwoColourDegreeMultiplicity
import RequestProject.Section31.EIGSTwoColourEdgeCountFormula
import RequestProject.Section2ScaleLimits
import Mathlib.Topology.Order.LiminfLimsup

/-! The ordinary logarithmic limit of the actual stationary degree fiber
counts, on the full occupied support, as in Li--Britz arXiv:2109.14463v2,
Definitions 3.1--3.2. This is not merely a mass/degree ratio. No cited
scale-free theorem or degree-dimension conclusion is assumed. Candidate. -/

namespace EIGS
open Filter Topology
noncomputable section

theorem twoColourSystem_degree_multiplicity_growth (kind : Bool) (level : ℕ) :
    (3 + Real.sqrt 6) ^ level / 2 ≤
      (twoColourDegreeMultiplicity (twoColourDegreeSupportValue (kind, level)) : ℝ) ∧
    (twoColourDegreeMultiplicity (twoColourDegreeSupportValue (kind, level)) : ℝ) ≤
      4 * (3 + Real.sqrt 6) ^ level := by
  have red := twoColourSystem_red_edge_growth_bounds level
  have blue := twoColourSystem_blue_edge_upper level
  have blueNonnegative : 0 ≤ (chiCount twoColourSystem.toRuleData level 1 : ℝ) := by positivity
  have powerNonnegative : 0 ≤ (3 + Real.sqrt 6) ^ level := by positivity
  cases kind
  · cases level with
    | zero =>
        have zeroValue : twoColourDegreeSupportValue (false, 0) = (2 / 3 : ℝ) := by
          norm_num [twoColourDegreeSupportValue]
        rw [zeroValue]
        rw [twoColourSystem_degree_two_zero_multiplicity]
        norm_num [chiCount_zero, twoColourSystem, EIGSData.toRuleData]
    | succ level =>
        change (3 + Real.sqrt 6) ^ (level + 1) / 2 ≤
          (twoColourDegreeMultiplicity ((2 / 3) / (2 : ℝ) ^ (level + 1)) : ℝ) ∧
          (twoColourDegreeMultiplicity ((2 / 3) / (2 : ℝ) ^ (level + 1)) : ℝ) ≤
            4 * (3 + Real.sqrt 6) ^ (level + 1)
        rw [twoColourSystem_degree_two_positive_multiplicity]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        constructor <;> nlinarith
  · change (3 + Real.sqrt 6) ^ level / 2 ≤
      (twoColourDegreeMultiplicity (1 / (2 : ℝ) ^ level) : ℝ) ∧
      (twoColourDegreeMultiplicity (1 / (2 : ℝ) ^ level) : ℝ) ≤
        4 * (3 + Real.sqrt 6) ^ level
    rw [twoColourSystem_degree_three_multiplicity]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    constructor <;> nlinarith

theorem twoColourSystem_normalized_degree_range :
    Set.range twoColourStationaryNormalizedDegree = Set.range twoColourDegreeSupportValue := by
  apply Set.Subset.antisymm twoColourSystem_normalized_degree_range_subset
  rintro degree ⟨⟨kind, level⟩, rfl⟩
  letI := twoColourSystem_normalized_degree_fiber_finite (kind, level)
  have positiveReal : 0 < (twoColourDegreeMultiplicity
      (twoColourDegreeSupportValue (kind, level)) : ℝ) :=
    (by positivity : 0 < (3 + Real.sqrt 6) ^ level / 2).trans_le
      (twoColourSystem_degree_multiplicity_growth kind level).1
  have positiveNatural : 0 < Nat.card {vertex : XiVertexUnion twoColourSystem //
      twoColourStationaryNormalizedDegree vertex = twoColourDegreeSupportValue (kind, level)} := by
    change 0 < twoColourDegreeMultiplicity (twoColourDegreeSupportValue (kind, level))
    exact_mod_cast positiveReal
  obtain ⟨vertex⟩ := Finite.card_pos_iff.mp positiveNatural
  exact ⟨vertex.val, vertex.property⟩

theorem twoColourDegreeSupport_inverse (kind : Bool) (level : ℕ) :
    (twoColourDegreeSupportValue (kind, level))⁻¹ =
      (if kind then 1 else (3 / 2 : ℝ)) * (2 : ℝ) ^ level := by
  cases kind <;> simp [twoColourDegreeSupportValue, div_eq_mul_inv, mul_comm]

theorem twoColourSystem_degree_dimension_ladder_limit (kind : Bool) :
    Tendsto (fun level : ℕ =>
      Real.log (twoColourDegreeMultiplicity (twoColourDegreeSupportValue (kind, level)) : ℝ) /
        (-Real.log (twoColourDegreeSupportValue (kind, level))))
      atTop (𝓝 (Real.log (3 + Real.sqrt 6) / Real.log 2)) := by
  have coefficientPositive : 0 < (if kind then 1 else (3 / 2 : ℝ)) := by
    cases kind <;> norm_num
  have radiusTendsto : Tendsto
      (fun level : ℕ => (twoColourDegreeSupportValue (kind, level))⁻¹) atTop atTop := by
    simp only [twoColourDegreeSupport_inverse]
    exact Tendsto.const_mul_atTop coefficientPositive
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have actual := logarithmic_ratio_limit_of_geometric_scale
    (sequence := fun level : ℕ =>
      (twoColourDegreeMultiplicity (twoColourDegreeSupportValue (kind, level)) : ℝ))
    (radius := fun level : ℕ => (twoColourDegreeSupportValue (kind, level))⁻¹)
    (depth := fun level : ℕ => level)
    (rate := 3 + Real.sqrt 6) (distance_rate := 2)
    (lower := 1 / 2) (upper := 4)
    (radius_lower := if kind then 1 else (3 / 2 : ℝ))
    (radius_upper := if kind then 1 else (3 / 2 : ℝ))
    (by positivity) (by norm_num) (by norm_num) (by norm_num)
    coefficientPositive coefficientPositive radiusTendsto
    (Eventually.of_forall (fun level => by
      simpa only [div_eq_mul_inv, mul_comm, one_mul] using twoColourSystem_degree_multiplicity_growth kind level))
    (Eventually.of_forall (fun level => by
      change (if kind then 1 else (3 / 2 : ℝ)) * (2 : ℝ) ^ level ≤
          (twoColourDegreeSupportValue (kind, level))⁻¹ ∧
        (twoColourDegreeSupportValue (kind, level))⁻¹ ≤
          (if kind then 1 else (3 / 2 : ℝ)) * (2 : ℝ) ^ level
      rw [twoColourDegreeSupport_inverse]
      exact ⟨le_rfl, le_rfl⟩))
  simpa only [Real.log_inv] using actual

theorem twoColourDegreeSupport_limit_of_ladder_limits {function : ℝ → ℝ} {value : ℝ}
    (low : Tendsto (fun level => function (twoColourDegreeSupportValue (false, level))) atTop (𝓝 value))
    (high : Tendsto (fun level => function (twoColourDegreeSupportValue (true, level))) atTop (𝓝 value)) :
    Tendsto function (𝓝[Set.range twoColourDegreeSupportValue] (0 : ℝ)) (𝓝 value) := by
  apply Metric.tendsto_nhdsWithin_nhds.2
  intro epsilon epsilonPositive
  obtain ⟨lowThreshold, lowBound⟩ := Metric.tendsto_atTop.1 low epsilon epsilonPositive
  obtain ⟨highThreshold, highBound⟩ := Metric.tendsto_atTop.1 high epsilon epsilonPositive
  let threshold := max lowThreshold highThreshold
  refine ⟨(2 / 3 : ℝ) / 2 ^ threshold, by positivity, ?_⟩
  intro degree inSupport nearZero
  obtain ⟨⟨kind, level⟩, rfl⟩ := inSupport
  have degreePositive : 0 < twoColourDegreeSupportValue (kind, level) := by
    cases kind <;> simp [twoColourDegreeSupportValue] <;> positivity
  have levelLarge : threshold ≤ level := by
    by_contra notLarge
    have levelSmall : level ≤ threshold := (Nat.lt_of_not_ge notLarge).le
    have powerBound : (2 : ℝ) ^ level ≤ 2 ^ threshold :=
      pow_le_pow_right₀ (by norm_num) levelSmall
    have lower : (2 / 3 : ℝ) / 2 ^ threshold ≤ twoColourDegreeSupportValue (kind, level) := by
      have comparison : (2 / 3 : ℝ) / 2 ^ threshold ≤ (2 / 3 : ℝ) / 2 ^ level :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) powerBound
      cases kind
      · exact comparison
      · exact comparison.trans
          (div_le_div_of_nonneg_right (by norm_num : (2 / 3 : ℝ) ≤ 1) (by positivity))
    have strictUpper : twoColourDegreeSupportValue (kind, level) < (2 / 3 : ℝ) / 2 ^ threshold := by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos degreePositive] using nearZero
    exact (not_lt_of_ge lower) strictUpper
  cases kind
  · exact lowBound level ((le_max_left _ _).trans levelLarge)
  · exact highBound level ((le_max_right _ _).trans levelLarge)

theorem twoColourSystem_actual_degree_dimension_limit :
    Tendsto (fun degree : ℝ => Real.log (twoColourDegreeMultiplicity degree : ℝ) / (-Real.log degree))
      (𝓝[Set.range twoColourStationaryNormalizedDegree] (0 : ℝ))
      (𝓝 (Real.log (3 + Real.sqrt 6) / Real.log 2)) := by
  rw [twoColourSystem_normalized_degree_range]
  exact twoColourDegreeSupport_limit_of_ladder_limits
    (twoColourSystem_degree_dimension_ladder_limit false)
    (twoColourSystem_degree_dimension_ladder_limit true)

theorem twoColourSystem_actual_degree_dimension_positive :
    0 < Real.log (3 + Real.sqrt 6) / Real.log 2 := by
  apply div_pos
  · exact Real.log_pos (by nlinarith [Real.sqrt_nonneg (6 : ℝ)])
  · exact Real.log_pos (by norm_num)

def twoColourOccupiedDegreeSupport : Set ℝ :=
  {degree | 0 < degree ∧ 0 < twoColourDegreeMultiplicity degree}

theorem twoColourSystem_occupied_degree_support :
    twoColourOccupiedDegreeSupport = Set.range twoColourStationaryNormalizedDegree := by
  apply Set.Subset.antisymm
  · intro degree occupied
    have positiveNatural : 0 < Nat.card {vertex : XiVertexUnion twoColourSystem //
        twoColourStationaryNormalizedDegree vertex = degree} := occupied.2
    letI := Nat.finite_of_card_ne_zero positiveNatural.ne'
    obtain ⟨vertex⟩ := Finite.card_pos_iff.mp positiveNatural
    exact ⟨vertex.val, vertex.property⟩
  · intro degree inRange
    rw [twoColourSystem_normalized_degree_range] at inRange
    obtain ⟨⟨kind, level⟩, rfl⟩ := inRange
    have positiveReal : 0 < (twoColourDegreeMultiplicity
        (twoColourDegreeSupportValue (kind, level)) : ℝ) :=
      (by positivity : 0 < (3 + Real.sqrt 6) ^ level / 2).trans_le
        (twoColourSystem_degree_multiplicity_growth kind level).1
    refine ⟨?_, ?_⟩
    · cases kind <;> simp [twoColourDegreeSupportValue] <;> positivity
    · exact_mod_cast positiveReal

theorem twoColourSystem_occupied_degree_support_accumulates :
    NeBot (𝓝[twoColourOccupiedDegreeSupport] (0 : ℝ)) := by
  rw [twoColourSystem_occupied_degree_support, twoColourSystem_normalized_degree_range]
  have approachZero : Tendsto (fun level : ℕ => twoColourDegreeSupportValue (true, level))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [twoColourDegreeSupportValue, ↓reduceIte, one_div] using
      tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have approachSupport : Tendsto (fun level : ℕ => twoColourDegreeSupportValue (true, level))
      atTop (𝓝[Set.range twoColourDegreeSupportValue] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨approachZero, Eventually.of_forall
      (fun level => ⟨(true, level), rfl⟩)⟩
  exact approachSupport.neBot

theorem twoColourSystem_original_degree_dimension_limit :
    Tendsto (fun degree : ℝ => Real.log (twoColourDegreeMultiplicity degree : ℝ) / (-Real.log degree))
      (𝓝[twoColourOccupiedDegreeSupport] (0 : ℝ))
      (𝓝 (Real.log (3 + Real.sqrt 6) / Real.log 2)) := by
  rw [twoColourSystem_occupied_degree_support]
  exact twoColourSystem_actual_degree_dimension_limit

theorem twoColourSystem_original_degree_dimension_limsup :
    Filter.limsup (fun degree : ℝ =>
      Real.log (twoColourDegreeMultiplicity degree : ℝ) / (-Real.log degree))
      (𝓝[twoColourOccupiedDegreeSupport] (0 : ℝ)) =
      Real.log (3 + Real.sqrt 6) / Real.log 2 := by
  letI := twoColourSystem_occupied_degree_support_accumulates
  exact twoColourSystem_original_degree_dimension_limit.limsup_eq

end
end EIGS

#print axioms EIGS.twoColourSystem_normalized_degree_range
#print axioms EIGS.twoColourSystem_degree_dimension_ladder_limit
#print axioms EIGS.twoColourSystem_actual_degree_dimension_limit
#print axioms EIGS.twoColourSystem_actual_degree_dimension_positive
#print axioms EIGS.twoColourSystem_original_degree_dimension_limit
#print axioms EIGS.twoColourSystem_original_degree_dimension_limsup
