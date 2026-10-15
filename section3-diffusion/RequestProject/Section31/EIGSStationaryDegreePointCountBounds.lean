import RequestProject.Section31.EIGSStationaryDegreeFiber
import RequestProject.Section31.EIGSColourEdgeGrowth
import RequestProject.Section31.EIGSVertexMassLimits

/-! Bounds for the actual global stationary degree point count at every
private birth ladder value. Colliding types are summed, while the two
initial endpoints are included in the upper bound. Candidate source. -/

namespace EIGS
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

def xiStationaryDegreeMultiplicity (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (coefficient rate normalizer value : ℝ) : ℕ :=
  Nat.card {vertex : XiVertexUnion system //
    xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer vertex = value}

theorem xiPrivateBirthType_nonempty (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour)) : Nonempty (XiPrivateBirthType system) := by
  letI : Nontrivial (system.rule system.initCol).V :=
    ⟨⟨system.plantPlus system.initCol, system.plantMinus system.initCol, system.plant_ne system.initCol⟩⟩
  obtain ⟨vertex, adjacency⟩ := (connected system.initCol).preconnected.exists_adj_of_nontrivial
    (system.plantPlus system.initCol)
  refine ⟨⟨system.initCol, ⟨vertex, adjacency.ne', ?_⟩⟩⟩
  intro equality
  apply plantingNonadjacent system.initCol
  simpa only [equality] using adjacency

theorem xiStationaryDegree_point_count_bounds (system : EIGSData K)
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
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ kind : XiPrivateBirthType system, ∀ level : ℕ, 1 ≤ level →
        lower * mass.rate ^ level ≤
          (xiStationaryDegreeMultiplicity system weights coefficient rate normalizer
            (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind / rate ^ level) : ℝ) ∧
        (xiStationaryDegreeMultiplicity system weights coefficient rate normalizer
          (xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer kind / rate ^ level) : ℝ) ≤
            upper * mass.rate ^ level := by
  letI : Nonempty (XiPrivateBirthType system) := xiPrivateBirthType_nonempty system connected plantingNonadjacent
  let coefficients := xiPrivateDegreeLadderCoefficient system weights coefficient rate normalizer
  have coefficientsPositive := xiPrivateDegreeLadderCoefficient_positive system connected distancePositive
    weights weightsPositive coefficient rate normalizer coefficientPositive
    (zero_lt_one.trans rateGreaterThanOne) normalizerPositive
  have massAtLeastOne : 1 ≤ mass.rate := (by norm_num : (1 : ℝ) ≤ 2).trans
    (XiMassParameters.rate_ge_two system connected plantingNonadjacent mass)
  obtain ⟨lower, _, lowerPositive, _, colourGrowth⟩ :=
    colour_edge_geometric_growth system connected distancePositive mass
  obtain ⟨_, upper, _, upperPositive, totalGrowth⟩ :=
    mass_geometric_growth system mass.amplitude_positive mass.eigenpair mass.rate_positive
  have colourUpper : ∀ level colour, (chiCount system.toRuleData level colour : ℝ) ≤ upper * mass.rate ^ level := by
    intro level colour
    apply le_trans _ (totalGrowth level).2
    rw [totalEdges_eq_sum]
    exact Finset.single_le_sum (fun oldColour _ => (Nat.cast_nonneg _ :
      0 ≤ chiVec system.toRuleData level oldColour)) (Finset.mem_univ colour)
  obtain ⟨offset, collisions⟩ := finite_geometric_ladder_collision_offsets coefficients coefficientsPositive
    rate rateGreaterThanOne
  refine ⟨lower, 2 + (Fintype.card (XiPrivateBirthType system) : ℝ) * upper * mass.rate ^ offset,
    lowerPositive, by positivity, ?_⟩
  intro kind level levelPositive
  let value := coefficients kind / rate ^ level
  letI : Finite {vertex : XiVertexUnion system //
      xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer vertex = value} :=
    xiStationaryDegree_fiber_finite system connected distancePositive weights weightsPositive
      coefficient rate normalizer coefficientPositive rateGreaterThanOne normalizerPositive value
  letI : Fintype {vertex : XiVertexUnion system //
      xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer vertex = value} := Fintype.ofFinite _
  letI : Finite (XiStationaryDegreeCode system weights coefficient rate normalizer value) :=
    (finite_geometric_ladder_fiber_bound coefficients coefficientsPositive rate rateGreaterThanOne value).1
  letI : Fintype (XiStationaryDegreeCode system weights coefficient rate normalizer value) := Fintype.ofFinite _
  constructor
  · let embed : {vertex : XiNewVertices system level // xiPrivateBirthTypeOf system level vertex = kind} →
        {vertex : XiVertexUnion system //
          xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer vertex = value} :=
      fun vertex => ⟨Sum.inr ⟨level, vertex.val⟩, by
        rw [xiStationaryDegree_private_birth_formula, vertex.property]⟩
    have injective : Function.Injective embed := by
      intro first second equality
      apply Subtype.ext
      exact eq_of_heq (Sigma.mk.inj_iff.1 (Sum.inr.inj (congrArg Subtype.val equality))).2
    have lowerNatural := Nat.card_le_card_of_injective embed injective
    rw [Nat.card_eq_fintype_card, xiPrivateBirthType_fiber_count] at lowerNatural
    have lowerReal : (chiCount system.toRuleData level kind.1 : ℝ) ≤
        (xiStationaryDegreeMultiplicity system weights coefficient rate normalizer value : ℝ) := by
      exact_mod_cast lowerNatural
    obtain ⟨age, rfl⟩ : ∃ age, level = age + 1 := ⟨level - 1, by omega⟩
    exact ((colourGrowth age kind.1).1).trans lowerReal
  · have countIdentity :
        (xiStationaryDegreeMultiplicity system weights coefficient rate normalizer value : ℝ) =
          (Fintype.card {vertex : Bool //
            xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer (Sum.inl vertex) = value} : ℝ) +
          ∑ code : XiStationaryDegreeCode system weights coefficient rate normalizer value,
            (Fintype.card {vertex : XiNewVertices system code.val.2 //
              xiPrivateBirthTypeOf system code.val.2 vertex = code.val.1} : ℝ) := by
      have identity := Fintype.card_congr
        (xiStationaryDegreeFiberEquiv system weights coefficient rate normalizer value)
      rw [Fintype.card_sum, Fintype.card_sigma] at identity
      simpa only [xiStationaryDegreeMultiplicity, Nat.card_eq_fintype_card,
        Nat.cast_add, Nat.cast_sum] using congrArg (fun count : ℕ => (count : ℝ)) identity
    have initialBound : (Fintype.card {vertex : Bool //
        xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer (Sum.inl vertex) = value} : ℝ) ≤ 2 := by
      have bound := Fintype.card_subtype_le (fun vertex : Bool =>
        xiStationaryDegreeFromAmplitudes system weights coefficient rate normalizer (Sum.inl vertex) = value)
      exact_mod_cast bound
    have eachCode : ∀ code : XiStationaryDegreeCode system weights coefficient rate normalizer value,
        (Fintype.card {vertex : XiNewVertices system code.val.2 //
          xiPrivateBirthTypeOf system code.val.2 vertex = code.val.1} : ℝ) ≤ upper * mass.rate ^ (level + offset) := by
      intro code
      rw [xiPrivateBirthType_fiber_count]
      have levelBound := (collisions kind code.val.1 level code.val.2 code.property.symm).1
      exact (colourUpper code.val.2 code.val.1.1).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ massAtLeastOne levelBound) upperPositive.le)
    have codeCard :
        (Fintype.card (XiStationaryDegreeCode system weights coefficient rate normalizer value) : ℝ) ≤
          (Fintype.card (XiPrivateBirthType system) : ℝ) := by
      have bound := (finite_geometric_ladder_fiber_bound coefficients coefficientsPositive rate rateGreaterThanOne value).2
      change Nat.card (XiStationaryDegreeCode system weights coefficient rate normalizer value) ≤
        Fintype.card (XiPrivateBirthType system) at bound
      rw [Nat.card_eq_fintype_card] at bound
      exact_mod_cast bound
    calc
      (xiStationaryDegreeMultiplicity system weights coefficient rate normalizer value : ℝ) ≤
          2 + ∑ _code : XiStationaryDegreeCode system weights coefficient rate normalizer value,
            upper * mass.rate ^ (level + offset) := by
        rw [countIdentity]
        exact add_le_add initialBound (Finset.sum_le_sum (fun code _ => eachCode code))
      _ = 2 + (Fintype.card (XiStationaryDegreeCode system weights coefficient rate normalizer value) : ℝ) *
          (upper * mass.rate ^ (level + offset)) := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ 2 + (Fintype.card (XiPrivateBirthType system) : ℝ) * (upper * mass.rate ^ (level + offset)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right codeCard
          (mul_nonneg upperPositive.le (pow_nonneg mass.rate_positive.le _)))
      _ ≤ (2 + (Fintype.card (XiPrivateBirthType system) : ℝ) * upper * mass.rate ^ offset) * mass.rate ^ level := by
        rw [pow_add]
        have oneBound : (1 : ℝ) ≤ mass.rate ^ level := one_le_pow₀ massAtLeastOne
        nlinarith

end
end EIGS

#print axioms EIGS.xiPrivateBirthType_nonempty
#print axioms EIGS.xiStationaryDegree_point_count_bounds
