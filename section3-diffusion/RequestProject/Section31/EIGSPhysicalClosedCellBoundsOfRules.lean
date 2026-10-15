import RequestProject.Section31.EIGSPhysicalClosedCellMassOfRules

/-! Uniform two-sided physical cell mass bounds at every generation. These
are consequences of the actual exact cell mass equality, not a cell-mass
input. The constants are common to every level and every actual edge. -/

namespace EIGS
open MeasureTheory
open scoped BigOperators
noncomputable section
variable {K : ℕ}

theorem exists_xiPhysicalClosedCell_mass_bounds_of_rules (system : EIGSData K)
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
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ coarse (ancestor : XiEdge system.toRuleData coarse),
        lower / mass.rate ^ coarse ≤
          (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
            (xiPhysicalClosedCell system connected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair coarse ancestor) ∧
          (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
            (xiPhysicalClosedCell system connected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair coarse ancestor) ≤
                upper / mass.rate ^ coarse := by
  intro parameters distanceGreaterThanOne mass
  obtain ⟨lower, lowerPositive, lowerBound⟩ :=
    exists_positive_colour_length_lower_bound system mass.amplitude mass.amplitude_positive
  have upperBound (colour : Fin K) : mass.amplitude colour ≤ ∑ other, mass.amplitude other :=
    Finset.single_le_sum (fun other _ => (mass.amplitude_positive other).le) (Finset.mem_univ colour)
  refine ⟨lower / mass.amplitude system.initCol,
    (∑ colour, mass.amplitude colour) / mass.amplitude system.initCol,
    div_pos lowerPositive (mass.amplitude_positive _),
    div_pos ((mass.amplitude_positive system.initCol).trans_le (upperBound system.initCol))
      (mass.amplitude_positive _), ?_⟩
  intro coarse ancestor
  have exactMass := xiPhysicalClosedCell_mass_eq_cylinder_of_rules system connected loopless unique
    plantingNonadjacent distancePositive primitiveDegree coarse ancestor
  have realMass :
      (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass).real
        (xiPhysicalClosedCell system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair coarse ancestor) =
            mass.edgeWeight coarse ancestor := by
    have mapped := congrArg ENNReal.toReal exactMass
    rw [ENNReal.toReal_ofReal (mass.edgeWeight_positive coarse ancestor).le] at mapped
    exact mapped
  rw [realMass]
  constructor
  · rw [div_div, mul_comm (mass.amplitude system.initCol), XiMassParameters.edgeWeight]
    exact div_le_div_of_nonneg_right (lowerBound _)
      (mul_pos (pow_pos mass.rate_positive coarse) (mass.amplitude_positive _)).le
  · rw [div_div, mul_comm (mass.amplitude system.initCol), XiMassParameters.edgeWeight]
    exact div_le_div_of_nonneg_right (upperBound _)
      (mul_pos (pow_pos mass.rate_positive coarse) (mass.amplitude_positive _)).le

end
end EIGS

#print axioms EIGS.exists_xiPhysicalClosedCell_mass_bounds_of_rules
