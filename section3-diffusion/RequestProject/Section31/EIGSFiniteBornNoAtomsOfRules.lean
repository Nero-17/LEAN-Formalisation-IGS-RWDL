import RequestProject.Section31.EIGSFiniteBornBallMassOfRules
import RequestProject.Section31.SmallBallPowerMassNoAtoms

/-! The actual completion measure has no atom at any finite-born vertex.
The positive local exponent and the physical ball upper estimate are supplied
from the original rule certificates, rather than assumed as target properties. -/

namespace EIGS
open MeasureTheory Metric IGS.Sec31
noncomputable section
variable {K : ℕ}

theorem xiFiniteBorn_singleton_mass_zero_of_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
    ∀ birth (vertex : XiVtx system birth),
      xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass
        {parameters.vertexEmbedding birth vertex} = 0 := by
  intro parameters distanceGreaterThanOne mass birth vertex
  have degreePositive : 0 < finiteRealMatrixSpectralRadius (degreeMatrix system) :=
    zero_lt_one.trans (degree_spectralRadius_gt_one_of_primitive system primitiveDegree)
  have degreeMass : finiteRealMatrixSpectralRadius (degreeMatrix system) < mass.rate := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass]
    exact degree_spectralRadius_lt_mass_of_primitive system connected loopless
      plantingNonadjacent distancePositive primitiveDegree
  have exponentPositive : 0 <
      (Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
        Real.log (system.distanceSpectralRadius connected) := by
    apply div_pos
    · exact sub_pos.mpr (Real.log_lt_log degreePositive degreeMass)
    · exact Real.log_pos distanceGreaterThanOne
  obtain ⟨lower, upper, threshold, lowerPositive, upperPositive, thresholdPositive, bounds⟩ :=
    exists_xiFiniteBornBallMass_of_rules system connected loopless unique plantingNonadjacent
      distancePositive primitiveDegree birth vertex
  exact singleton_mass_zero_of_small_ball_power_upper
    (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass)
    (parameters.vertexEmbedding birth vertex) _ upper threshold exponentPositive thresholdPositive
    (fun radius radiusPositive radiusSmall => (bounds radius radiusPositive radiusSmall).2)

theorem xiFiniteBornSkeleton_mass_zero_of_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
    xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass
      (⋃ birth : ℕ, Set.range (parameters.vertexEmbedding birth)) = 0 := by
  intro parameters distanceGreaterThanOne mass
  apply measure_iUnion_null
  intro birth
  have rangeEquality : Set.range (parameters.vertexEmbedding birth) =
      ⋃ vertex : XiVtx system birth, {parameters.vertexEmbedding birth vertex} := by
    ext point
    simp only [Set.mem_range, Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨fun ⟨vertex, equality⟩ => ⟨vertex, equality.symm⟩,
      fun ⟨vertex, equality⟩ => ⟨vertex, equality.symm⟩⟩
  rw [rangeEquality]
  apply measure_iUnion_null
  intro vertex
  exact xiFiniteBorn_singleton_mass_zero_of_rules system connected loopless unique
    plantingNonadjacent distancePositive primitiveDegree birth vertex

end
end EIGS

#print axioms EIGS.xiFiniteBorn_singleton_mass_zero_of_rules
#print axioms EIGS.xiFiniteBornSkeleton_mass_zero_of_rules
