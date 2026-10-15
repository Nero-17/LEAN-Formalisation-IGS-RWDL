import RequestProject.Section31.EIGSPrimitiveOriginalDegreeDimension
import RequestProject.Section31.SameFamilyKernelFullHeatEstimates

/-! Identify the correction in a supplied full-heat family with the original
global stationary degree point-count statistic. The supplied family, closed
semigroup and literal kernel are retained. The degree statistic and its
ordinary limit are constructed from the actual rules, without using the
external scale-free theorem. Candidate source, awaiting compilation. -/

namespace EIGS
open IGS.Sec31 MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical NNReal
noncomputable section
variable {K : ℕ}
variable {State : Type*} [MetricSpace State] [CompactSpace State]
    [MeasurableSpace State] [BorelSpace State]
local instance : MeasurableSpace C(ℝ≥0, State) := borel _
local instance : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

/-- The original degree dimension is the limsup of actual global point
counts on their occupied positive support (Li--Britz, Definition 3.2). -/
def xiOriginalStationaryDegreeDimension (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (coefficient rate normalizer : ℝ) : ℝ :=
  Filter.limsup (fun value : ℝ =>
    Real.log (xiStationaryDegreeMultiplicity system weights coefficient rate normalizer value : ℝ) /
      (-Real.log value))
    (𝓝[xiStationaryOccupiedDegreeSupport system weights coefficient rate normalizer] (0 : ℝ))

def XiOriginalDegreeSameFamilyFullHeat (system : EIGSData K)
    (weights : Fin K ⊕ Fin K → ℝ) (coefficient degreeRate normalizer massRate resistanceRate : ℝ)
    (measure : Measure State)
    (embedding : C(State, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (closedSemigroup : ℝ≥0 → Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State))))
    (vertices : ∀ level, XiVtx system level → State) : Prop :=
  (∀ vertex, 0 < xiStationaryDegreeFromAmplitudes system weights coefficient degreeRate normalizer vertex ∧
    xiStationaryDegreeFromAmplitudes system weights coefficient degreeRate normalizer vertex ≤ 1) ∧
  (∀ vertex, Tendsto (fun level => xiActualMaxNormalizedDegree system level vertex) atTop
    (𝓝 (xiStationaryDegreeFromAmplitudes system weights coefficient degreeRate normalizer vertex))) ∧
  (∀ value : ℝ, Finite {vertex : XiVertexUnion system //
    xiStationaryDegreeFromAmplitudes system weights coefficient degreeRate normalizer vertex = value}) ∧
  0 < xiOriginalStationaryDegreeDimension system weights coefficient degreeRate normalizer ∧
  Tendsto (fun value : ℝ =>
    Real.log (xiStationaryDegreeMultiplicity system weights coefficient degreeRate normalizer value : ℝ) /
      (-Real.log value))
    (𝓝[xiStationaryOccupiedDegreeSupport system weights coefficient degreeRate normalizer] (0 : ℝ))
    (𝓝 (xiOriginalStationaryDegreeDimension system weights coefficient degreeRate normalizer)) ∧
  NeBot (𝓝[xiStationaryOccupiedDegreeSupport system weights coefficient degreeRate normalizer] (0 : ℝ)) ∧
  SameFamilyFullHeatKernelProperties measure embedding closedSemigroup
    (Real.log massRate / Real.log (massRate * resistanceRate)) semigroup globalLaws familyMeasurable vertices
    ((Real.log massRate / Real.log (massRate * resistanceRate)) *
      (1 - 1 / xiOriginalStationaryDegreeDimension system weights coefficient degreeRate normalizer))
    (1 / (xiOriginalStationaryDegreeDimension system weights coefficient degreeRate normalizer - 1))

theorem primitive_rules_original_degree_same_family_full_heat (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitive : (degreeMatrix system).IsPrimitive)
    (mass : XiMassParameters system) (resistanceRate : ℝ)
    (measure : Measure State)
    (embedding : C(State, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (closedSemigroup : ℝ≥0 → Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (semigroup : ℝ≥0 → C(State, ℝ) →L[ℝ] C(State, ℝ))
    (globalLaws : State → ProbabilityMeasure C(ℝ≥0, State))
    (familyMeasurable : Measurable (fun start => (globalLaws start : Measure C(ℝ≥0, State))))
    (vertices : ∀ level, XiVtx system level → State)
    (sameFamily : SameFamilyFullHeatKernelProperties measure embedding closedSemigroup
      (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) semigroup globalLaws familyMeasurable vertices
      ((Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
        Real.log (mass.rate * resistanceRate))
      (1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1))) :
    ∃ weights : Fin K ⊕ Fin K → ℝ, ∃ coefficient normalizer : ℝ,
      XiOriginalDegreeSameFamilyFullHeat system weights coefficient
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer mass.rate resistanceRate
        measure embedding closedSemigroup semigroup globalLaws familyMeasurable vertices := by
  obtain ⟨weights, coefficient, normalizer, stationaryBounds, stationaryConvergence,
    fibersFinite, dimensionPositive, distributionLimit, supportAccumulates, dimensionEquality⟩ :=
      primitive_rules_original_degree_dimension system connected loopless unique plantingNonadjacent
        distancePositive primitive
  have massEquality := XiMassParameters.rate_eq_spectralRadius system mass
  rw [← massEquality] at dimensionPositive distributionLimit dimensionEquality
  have actualDimensionEquality :
      xiOriginalStationaryDegreeDimension system weights coefficient
        (finiteRealMatrixSpectralRadius (degreeMatrix system)) normalizer =
          Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) :=
    dimensionEquality
  have massLogNonzero : Real.log mass.rate ≠ 0 :=
    (Real.log_pos ((by norm_num : (1 : ℝ) < 2).trans_le
      (XiMassParameters.rate_ge_two system connected plantingNonadjacent mass))).ne'
  have degreeLogNonzero : Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) ≠ 0 :=
    (Real.log_pos (degree_spectralRadius_gt_one_of_primitive system primitive)).ne'
  have finiteExponentEquality :
      (Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
        Real.log (mass.rate * resistanceRate) =
      (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) *
        (1 - 1 / (Real.log mass.rate / Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)))) := by
    by_cases denominatorZero : Real.log (mass.rate * resistanceRate) = 0
    · simp only [denominatorZero, div_zero, zero_mul]
    · field_simp [massLogNonzero, degreeLogNonzero, denominatorZero] <;> ring
  refine ⟨weights, coefficient, normalizer, stationaryBounds, stationaryConvergence,
    fibersFinite, ?_, ?_, supportAccumulates, ?_⟩
  · rw [actualDimensionEquality]
    exact dimensionPositive
  · rw [actualDimensionEquality]
    exact distributionLimit
  · rw [actualDimensionEquality, ← finiteExponentEquality]
    exact sameFamily

end
end EIGS

#print axioms EIGS.primitive_rules_original_degree_same_family_full_heat
