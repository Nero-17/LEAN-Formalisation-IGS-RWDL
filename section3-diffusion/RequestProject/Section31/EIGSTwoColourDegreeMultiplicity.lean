import RequestProject.Section31.EIGSTwoColourNormalizedDegreeSupport

/-! Actual cardinalities of stationary degree fibers, rather than a scalar
substitute for degree dimension. Finite birth classes give finite fibers.
Candidate source. -/

namespace EIGS
open scoped Classical
noncomputable section

def twoColourDegreeThreeIndexFiberEquiv (level : ℕ) :
    {vertex : XiVertexUnion twoColourSystem // twoColourVertexDegreeIndex vertex = (true, level)} ≃
    {vertex : XiNewVertices twoColourSystem level // twoColourBirthDegreeThree level vertex} where
  toFun vertex := by
    rcases vertex with ⟨vertex, property⟩
    rcases vertex with original | ⟨birth, privateVertex⟩
    · simp [twoColourVertexDegreeIndex] at property
    · by_cases high : twoColourBirthDegreeThree birth privateVertex
      · have birthEquality : birth = level := by
          have equality := congrArg Prod.snd property
          simpa only [twoColourVertexDegreeIndex, if_pos high] using equality
        subst birth
        exact ⟨privateVertex, high⟩
      · simp [twoColourVertexDegreeIndex, high] at property
  invFun vertex := ⟨Sum.inr ⟨level, vertex.val⟩, by simp [twoColourVertexDegreeIndex, vertex.property]⟩
  left_inv := by
    rintro ⟨vertex, property⟩
    apply Subtype.ext
    rcases vertex with original | ⟨birth, privateVertex⟩
    · simp [twoColourVertexDegreeIndex] at property
    · by_cases high : twoColourBirthDegreeThree birth privateVertex
      · have birthEquality : birth = level := by
          have equality := congrArg Prod.snd property
          simpa only [twoColourVertexDegreeIndex, if_pos high] using equality
        subst birth
        simp only [dif_pos high]
      · simp [twoColourVertexDegreeIndex, high] at property
  right_inv := by
    rintro ⟨privateVertex, high⟩
    apply Subtype.ext
    simp only [dif_pos high]

def twoColourDegreeTwoPositiveIndexFiberEquiv (level : ℕ) :
    {vertex : XiVertexUnion twoColourSystem // twoColourVertexDegreeIndex vertex = (false, level + 1)} ≃
    {vertex : XiNewVertices twoColourSystem (level + 1) //
      ¬ twoColourBirthDegreeThree (level + 1) vertex} where
  toFun vertex := by
    rcases vertex with ⟨vertex, property⟩
    rcases vertex with original | ⟨birth, privateVertex⟩
    · simp [twoColourVertexDegreeIndex] at property
    · by_cases high : twoColourBirthDegreeThree birth privateVertex
      · rw [twoColourVertexDegreeIndex, if_pos high] at property
        have impossible : (true : Bool) = false := congrArg Prod.fst property
        cases impossible
      · have birthEquality : birth = level + 1 := by
          have equality := congrArg Prod.snd property
          simpa only [twoColourVertexDegreeIndex, if_neg high] using equality
        subst birth
        exact ⟨privateVertex, high⟩
  invFun vertex := ⟨Sum.inr ⟨level + 1, vertex.val⟩,
    by simp [twoColourVertexDegreeIndex, vertex.property]⟩
  left_inv := by
    rintro ⟨vertex, property⟩
    apply Subtype.ext
    rcases vertex with original | ⟨birth, privateVertex⟩
    · simp [twoColourVertexDegreeIndex] at property
    · by_cases high : twoColourBirthDegreeThree birth privateVertex
      · rw [twoColourVertexDegreeIndex, if_pos high] at property
        have impossible : (true : Bool) = false := congrArg Prod.fst property
        cases impossible
      · have birthEquality : birth = level + 1 := by
          have equality := congrArg Prod.snd property
          simpa only [twoColourVertexDegreeIndex, if_neg high] using equality
        subst birth
        simp only [dif_neg high]
  right_inv := by
    rintro ⟨privateVertex, high⟩
    apply Subtype.ext
    simp only [dif_neg high]

def twoColourDegreeTwoZeroIndexFiberEquiv :
    {vertex : XiVertexUnion twoColourSystem // twoColourVertexDegreeIndex vertex = (false, 0)} ≃
    Bool ⊕ {vertex : XiNewVertices twoColourSystem 0 // ¬ twoColourBirthDegreeThree 0 vertex} where
  toFun vertex := by
    rcases vertex with ⟨vertex, property⟩
    rcases vertex with original | ⟨birth, privateVertex⟩
    · exact Sum.inl original
    · by_cases high : twoColourBirthDegreeThree birth privateVertex
      · rw [twoColourVertexDegreeIndex, if_pos high] at property
        have impossible : (true : Bool) = false := congrArg Prod.fst property
        cases impossible
      · have birthEquality : birth = 0 := by
          have equality := congrArg Prod.snd property
          simpa only [twoColourVertexDegreeIndex, if_neg high] using equality
        subst birth
        exact Sum.inr ⟨privateVertex, high⟩
  invFun vertex := match vertex with
    | Sum.inl original => ⟨Sum.inl original, rfl⟩
    | Sum.inr privateVertex => ⟨Sum.inr ⟨0, privateVertex.val⟩,
        by simp [twoColourVertexDegreeIndex, privateVertex.property]⟩
  left_inv := by
    rintro ⟨vertex, property⟩
    apply Subtype.ext
    rcases vertex with original | ⟨birth, privateVertex⟩
    · rfl
    · by_cases high : twoColourBirthDegreeThree birth privateVertex
      · rw [twoColourVertexDegreeIndex, if_pos high] at property
        have impossible : (true : Bool) = false := congrArg Prod.fst property
        cases impossible
      · have birthEquality : birth = 0 := by
          have equality := congrArg Prod.snd property
          simpa only [twoColourVertexDegreeIndex, if_neg high] using equality
        subst birth
        simp only [dif_neg high]
  right_inv := by
    intro vertex
    rcases vertex with original | ⟨privateVertex, high⟩
    · rfl
    · simp only [dif_neg high]

def twoColourDegreeMultiplicity (degree : ℝ) : ℕ :=
  Nat.card {vertex : XiVertexUnion twoColourSystem //
    twoColourStationaryNormalizedDegree vertex = degree}

theorem twoColourSystem_degree_three_multiplicity (level : ℕ) :
    twoColourDegreeMultiplicity (1 / (2 : ℝ) ^ level) =
      2 * chiCount twoColourSystem.toRuleData level 0 := by
  change Nat.card {vertex : XiVertexUnion twoColourSystem //
    twoColourStationaryNormalizedDegree vertex = twoColourDegreeSupportValue (true, level)} = _
  rw [Nat.card_congr ((twoColourNormalizedDegreeFiberEquiv (true, level)).trans
    (twoColourDegreeThreeIndexFiberEquiv level)), Nat.card_eq_fintype_card]
  exact twoColourSystem_birth_degree_three_count level

theorem twoColourSystem_degree_two_positive_multiplicity (level : ℕ) :
    twoColourDegreeMultiplicity ((2 / 3) / (2 : ℝ) ^ (level + 1)) =
      chiCount twoColourSystem.toRuleData (level + 1) 0 +
        3 * chiCount twoColourSystem.toRuleData (level + 1) 1 := by
  change Nat.card {vertex : XiVertexUnion twoColourSystem //
    twoColourStationaryNormalizedDegree vertex =
      twoColourDegreeSupportValue (false, level + 1)} = _
  rw [Nat.card_congr ((twoColourNormalizedDegreeFiberEquiv (false, level + 1)).trans
    (twoColourDegreeTwoPositiveIndexFiberEquiv level)), Nat.card_eq_fintype_card]
  exact twoColourSystem_birth_degree_two_count (level + 1)

theorem twoColourSystem_degree_two_zero_multiplicity :
    twoColourDegreeMultiplicity (2 / 3) =
      2 + chiCount twoColourSystem.toRuleData 0 0 +
        3 * chiCount twoColourSystem.toRuleData 0 1 := by
  have zeroValue : twoColourDegreeSupportValue (false, 0) = (2 / 3 : ℝ) := by
    norm_num [twoColourDegreeSupportValue]
  rw [← zeroValue]
  change Nat.card {vertex : XiVertexUnion twoColourSystem //
    twoColourStationaryNormalizedDegree vertex = twoColourDegreeSupportValue (false, 0)} = _
  rw [Nat.card_congr ((twoColourNormalizedDegreeFiberEquiv (false, 0)).trans
    twoColourDegreeTwoZeroIndexFiberEquiv), Nat.card_eq_fintype_card, Fintype.card_sum,
    Fintype.card_bool, twoColourSystem_birth_degree_two_count]
  omega

theorem twoColourSystem_normalized_degree_fiber_finite (index : Bool × ℕ) :
    Finite {vertex : XiVertexUnion twoColourSystem //
      twoColourStationaryNormalizedDegree vertex = twoColourDegreeSupportValue index} := by
  rcases index with ⟨kind, level⟩
  cases kind
  · cases level with
    | zero =>
        exact Finite.of_equiv _ (((twoColourNormalizedDegreeFiberEquiv (false, 0)).trans
          twoColourDegreeTwoZeroIndexFiberEquiv).symm)
    | succ level =>
        exact Finite.of_equiv _ (((twoColourNormalizedDegreeFiberEquiv (false, level + 1)).trans
          (twoColourDegreeTwoPositiveIndexFiberEquiv level)).symm)
  · exact Finite.of_equiv _ (((twoColourNormalizedDegreeFiberEquiv (true, level)).trans
      (twoColourDegreeThreeIndexFiberEquiv level)).symm)

end
end EIGS

#print axioms EIGS.twoColourSystem_degree_three_multiplicity
#print axioms EIGS.twoColourSystem_degree_two_positive_multiplicity
#print axioms EIGS.twoColourSystem_degree_two_zero_multiplicity
#print axioms EIGS.twoColourSystem_normalized_degree_fiber_finite
