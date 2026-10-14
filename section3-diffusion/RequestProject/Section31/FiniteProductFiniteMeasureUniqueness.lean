import RequestProject.Section31.FiniteSupportPathProductUniqueness

/-! Finite continuous product tests determine arbitrary finite measures on
a compact finite product, including measures of total mass zero. -/

namespace IGS.Sec31.FiniteProductWeak

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators Classical BoundedContinuousFunction NNReal ENNReal
noncomputable section
set_option maxHeartbeats 4000000

theorem finiteMeasure_eq_of_product_integrals
    {Coordinates State : Type*} [Fintype Coordinates] [MetricSpace State] [CompactSpace State]
    [MeasurableSpace State] [BorelSpace State]
    (first second : Measure (Coordinates → State)) [IsFiniteMeasure first] [IsFiniteMeasure second]
    (sameProducts : ∀ tests : Coordinates → State →ᵇ ℝ,
      (∫ point, ∏ coordinate, tests coordinate (point coordinate) ∂first) =
        ∫ point, ∏ coordinate, tests coordinate (point coordinate) ∂second) :
    first = second := by
  rcases isEmpty_or_nonempty (Coordinates → State) with empty | nonempty
  · letI := empty
    exact first.eq_zero_of_isEmpty.trans second.eq_zero_of_isEmpty.symm
  letI := nonempty
  let firstFinite : FiniteMeasure (Coordinates → State) := ⟨first, inferInstance⟩
  let secondFinite : FiniteMeasure (Coordinates → State) := ⟨second, inferInstance⟩
  have realMassEquality : (first Set.univ).toReal = (second Set.univ).toReal := by
    simpa using sameProducts (fun _ => 1)
  have massEquality : firstFinite.mass = secondFinite.mass := by
    have univEquality : first Set.univ = second Set.univ :=
      (ENNReal.toReal_eq_toReal_iff' (measure_ne_top first Set.univ) (measure_ne_top second Set.univ)).mp
        realMassEquality
    exact congrArg ENNReal.toNNReal univEquality
  by_cases firstZero : firstFinite = 0
  · have secondZero : secondFinite = 0 :=
      (FiniteMeasure.mass_zero_iff secondFinite).mp (by rw [← massEquality, firstZero, FiniteMeasure.zero_mass])
    exact congrArg FiniteMeasure.toMeasure (firstZero.trans secondZero.symm)
  have secondNonzero : secondFinite ≠ 0 := by
    intro secondZero
    apply firstZero
    exact (FiniteMeasure.mass_zero_iff firstFinite).mp (by rw [massEquality, secondZero, FiniteMeasure.zero_mass])
  have normalizedEquality : firstFinite.normalize = secondFinite.normalize := by
    apply probability_eq_of_product_integrals
    intro tests
    rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero firstFinite firstZero,
      FiniteMeasure.toMeasure_normalize_eq_of_nonzero secondFinite secondNonzero]
    change (∫ point, ∏ coordinate, tests coordinate (point coordinate)
      ∂(((firstFinite.mass⁻¹ : ℝ≥0) : ℝ≥0∞) • first)) =
      ∫ point, ∏ coordinate, tests coordinate (point coordinate)
        ∂(((secondFinite.mass⁻¹ : ℝ≥0) : ℝ≥0∞) • second)
    rw [integral_smul_measure, integral_smul_measure, massEquality, sameProducts tests]
  have finiteEquality : firstFinite = secondFinite := by
    calc
      firstFinite = firstFinite.mass • firstFinite.normalize.toFiniteMeasure :=
        firstFinite.self_eq_mass_smul_normalize
      _ = secondFinite.mass • secondFinite.normalize.toFiniteMeasure := by
        rw [massEquality, normalizedEquality]
      _ = secondFinite := secondFinite.self_eq_mass_smul_normalize.symm
  exact congrArg FiniteMeasure.toMeasure finiteEquality

end
end IGS.Sec31.FiniteProductWeak

#print axioms IGS.Sec31.FiniteProductWeak.finiteMeasure_eq_of_product_integrals
