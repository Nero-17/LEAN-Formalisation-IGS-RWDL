import RequestProject.Section31.EIGSTwoColourDegreeDimension
import RequestProject.Section31.EIGSTwoColourMatrixSpectra
import RequestProject.Section31.SameFamilyKernelFullHeatEstimates

/-! Original degree statistics in the same supplied two-colour full-heat
family. The actual nonprimitive graph uses its proved global point-count
limit, not a primitive-degree theorem. No new kernel or process is chosen.
Candidate source, awaiting compilation. -/

namespace EIGS
open IGS.Sec31 MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical NNReal
noncomputable section
variable {State : Type*} [MetricSpace State] [CompactSpace State]
    [MeasurableSpace State] [BorelSpace State]
local instance twoColourOriginalDegreeGlobalPathMeasurable : MeasurableSpace C(ℝ≥0, State) := borel _
local instance twoColourOriginalDegreeGlobalPathBorel : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

def twoColourOriginalDegreeDimension : ℝ :=
  Filter.limsup (fun value : ℝ =>
    Real.log (twoColourDegreeMultiplicity value : ℝ) / (-Real.log value))
    (𝓝[twoColourOccupiedDegreeSupport] (0 : ℝ))

theorem twoColourSystem_original_degree_same_family_full_heat
    (mass : XiMassParameters twoColourSystem) (resistanceRate : ℝ)
    (measure : Measure State)
    (embedding : C(State, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (closedSemigroup : ℝ≥0 → Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State))))
    (vertices : ∀ level, XiVtx twoColourSystem level → State)
    (sameFamily : SameFamilyFullHeatKernelProperties measure embedding closedSemigroup
      (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) semigroup globalLaws familyMeasurable vertices
      ((Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix twoColourSystem))) /
        Real.log (mass.rate * resistanceRate))
      (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix twoColourSystem)) - 1))) :
    twoColourOriginalDegreeDimension = Real.log (3 + Real.sqrt 6) / Real.log 2 ∧
    0 < twoColourOriginalDegreeDimension ∧
    Tendsto (fun value : ℝ => Real.log (twoColourDegreeMultiplicity value : ℝ) / (-Real.log value))
      (𝓝[twoColourOccupiedDegreeSupport] (0 : ℝ)) (𝓝 twoColourOriginalDegreeDimension) ∧
    NeBot (𝓝[twoColourOccupiedDegreeSupport] (0 : ℝ)) ∧
    SameFamilyFullHeatKernelProperties measure embedding closedSemigroup
      (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) semigroup globalLaws familyMeasurable vertices
      ((Real.log mass.rate / Real.log (mass.rate * resistanceRate)) *
        (1 - 1 / twoColourOriginalDegreeDimension))
      (1 / (twoColourOriginalDegreeDimension - 1)) := by
  have canonicalDimensionEquality :
      twoColourOriginalDegreeDimension = Real.log (3 + Real.sqrt 6) / Real.log 2 :=
    twoColourSystem_original_degree_dimension_limsup
  have massEquality : mass.rate = 3 + Real.sqrt 6 :=
    (XiMassParameters.rate_eq_spectralRadius twoColourSystem mass).trans twoColourSystem_massSpectralRadius
  have actualDimensionEquality : twoColourOriginalDegreeDimension =
      Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix twoColourSystem)) := by
    rw [massEquality, twoColourSystem_degreeSpectralRadius]
    exact canonicalDimensionEquality
  have massLogNonzero : Real.log mass.rate ≠ 0 := by
    rw [massEquality]
    exact (Real.log_pos (by nlinarith [Real.sqrt_nonneg (6 : ℝ)])).ne'
  have degreeLogNonzero : Real.log (finiteRealMatrixSpectralRadius (degreeMatrix twoColourSystem)) ≠ 0 := by
    rw [twoColourSystem_degreeSpectralRadius]
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have finiteExponentEquality :
      (Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix twoColourSystem))) /
        Real.log (mass.rate * resistanceRate) =
      (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) *
        (1 - 1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix twoColourSystem)))) := by
    by_cases denominatorZero : Real.log (mass.rate * resistanceRate) = 0
    · simp only [denominatorZero, div_zero, zero_mul]
    · field_simp [massLogNonzero, degreeLogNonzero, denominatorZero] <;> ring
  refine ⟨canonicalDimensionEquality, ?_, ?_, twoColourSystem_occupied_degree_support_accumulates, ?_⟩
  · rw [canonicalDimensionEquality]
    exact twoColourSystem_actual_degree_dimension_positive
  · rw [canonicalDimensionEquality]
    exact twoColourSystem_original_degree_dimension_limit
  · rw [actualDimensionEquality, ← finiteExponentEquality]
    exact sameFamily

end
end EIGS

#print axioms EIGS.twoColourSystem_original_degree_same_family_full_heat
