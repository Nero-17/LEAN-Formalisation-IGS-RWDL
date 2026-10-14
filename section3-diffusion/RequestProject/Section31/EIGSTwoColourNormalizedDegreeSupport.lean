import RequestProject.Section31.EIGSTwoColourBirthDegreeCounts

/-! The two disjoint occupied-degree ladders and their faithful indexing.
The map factors the actual stationary degree, so its fibers can be counted
from the actual birth classes without replacing degree dimension by a scalar
definition. Candidate source. -/

namespace EIGS
open scoped Classical
noncomputable section

def twoColourDegreeSupportValue (index : Bool × ℕ) : ℝ :=
  if index.1 then 1 / (2 : ℝ) ^ index.2 else (2 / 3) / (2 : ℝ) ^ index.2

def twoColourVertexDegreeIndex : XiVertexUnion twoColourSystem → Bool × ℕ
  | Sum.inl _ => (false, 0)
  | Sum.inr ⟨level, privateVertex⟩ =>
      if twoColourBirthDegreeThree level privateVertex then (true, level) else (false, level)

theorem twoColourSystem_normalized_degree_factors (vertex : XiVertexUnion twoColourSystem) :
    twoColourStationaryNormalizedDegree vertex =
      twoColourDegreeSupportValue (twoColourVertexDegreeIndex vertex) := by
  rcases vertex with vertex | ⟨level, edge, privateVertex⟩
  · simp [twoColourSystem_original_normalized_degree,
      twoColourVertexDegreeIndex, twoColourDegreeSupportValue]
  · rw [twoColourSystem_private_normalized_degree]
    simp only [twoColourVertexDegreeIndex, twoColourBirthDegreeThree]
    split_ifs <;> simp [twoColourDegreeSupportValue]

theorem twoColourDegreeSupport_ladders_disjoint (first second : ℕ) :
    1 / (2 : ℝ) ^ first ≠ (2 / 3) / (2 : ℝ) ^ second := by
  intro equality
  field_simp at equality
  have naturalEquality : 3 * (2 : ℕ) ^ second = 2 * (2 : ℕ) ^ first := by
    exact_mod_cast equality
  have divisible : (3 : ℕ) ∣ 2 * (2 : ℕ) ^ first :=
    ⟨(2 : ℕ) ^ second, naturalEquality.symm⟩
  have prime : Nat.Prime 3 := by decide
  rcases prime.dvd_mul.mp divisible with dividesTwo | dividesPower
  · norm_num at dividesTwo
  · have dividesTwo := prime.dvd_of_dvd_pow dividesPower
    norm_num at dividesTwo

theorem twoColourDegreeSupportValue_injective :
    Function.Injective twoColourDegreeSupportValue := by
  rintro ⟨firstKind, first⟩ ⟨secondKind, second⟩ equality
  have powersInjective : Function.Injective (fun exponent : ℕ => (2 : ℝ) ^ exponent) :=
    pow_right_injective₀ (by norm_num) (by norm_num)
  cases firstKind <;> cases secondKind
  · have samePower : (2 : ℝ) ^ first = (2 : ℝ) ^ second := by
      simp only [twoColourDegreeSupportValue, Bool.false_eq_true, ↓reduceIte] at equality
      field_simp at equality
      linarith
    exact congrArg (fun exponent => (false, exponent)) (powersInjective samePower)
  · have collision : (2 / 3) / (2 : ℝ) ^ first = 1 / (2 : ℝ) ^ second := by
      simpa only [twoColourDegreeSupportValue, Bool.false_eq_true, ↓reduceIte] using equality
    exact False.elim (twoColourDegreeSupport_ladders_disjoint second first collision.symm)
  · have collision : 1 / (2 : ℝ) ^ first = (2 / 3) / (2 : ℝ) ^ second := by
      simpa only [twoColourDegreeSupportValue, Bool.false_eq_true, ↓reduceIte] using equality
    exact False.elim (twoColourDegreeSupport_ladders_disjoint first second collision)
  · have samePower : (2 : ℝ) ^ first = (2 : ℝ) ^ second := by
      simpa only [twoColourDegreeSupportValue, ↓reduceIte, one_div, inv_inj] using equality
    exact congrArg (fun exponent => (true, exponent)) (powersInjective samePower)

def twoColourNormalizedDegreeFiberEquiv (index : Bool × ℕ) :
    {vertex : XiVertexUnion twoColourSystem //
      twoColourStationaryNormalizedDegree vertex = twoColourDegreeSupportValue index} ≃
    {vertex : XiVertexUnion twoColourSystem // twoColourVertexDegreeIndex vertex = index} where
  toFun vertex := ⟨vertex.val, twoColourDegreeSupportValue_injective
    ((twoColourSystem_normalized_degree_factors vertex.val).symm.trans vertex.property)⟩
  invFun vertex := ⟨vertex.val, (twoColourSystem_normalized_degree_factors vertex.val).trans
    (congrArg twoColourDegreeSupportValue vertex.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem twoColourSystem_normalized_degree_range_subset :
    Set.range twoColourStationaryNormalizedDegree ⊆ Set.range twoColourDegreeSupportValue := by
  rintro degree ⟨vertex, rfl⟩
  exact ⟨twoColourVertexDegreeIndex vertex,
    (twoColourSystem_normalized_degree_factors vertex).symm⟩

end
end EIGS

#print axioms EIGS.twoColourDegreeSupport_ladders_disjoint
#print axioms EIGS.twoColourDegreeSupportValue_injective
#print axioms EIGS.twoColourNormalizedDegreeFiberEquiv
#print axioms EIGS.twoColourSystem_normalized_degree_range_subset
