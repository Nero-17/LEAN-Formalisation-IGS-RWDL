import RequestProject.Section31.EIGSPhysicalClosedCellBoundary
import RequestProject.Section31.EIGSFiniteBornNoAtomsOfRules

/-! Exact physical cell masses from the actual address law. Extra addresses
in a physical cell can only code its two coarse terminals, whose measure is
proved zero from the rule assumptions. The final equality has no physical
cell mass or nonatomicity assumption. -/

namespace EIGS
open MeasureTheory Filter Topology
noncomputable section
variable {K : ℕ}

theorem xiPhysicalClosedCell_mass_eq_cylinder (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)
    (mass : XiMassParameters system)
    (noFiniteBornAtoms : ∀ birth (vertex : XiVtx system birth),
      xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
        {xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair birth vertex} = 0)
    (coarse : ℕ) (ancestor : XiEdge system.toRuleData coarse) :
    xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
      (xiPhysicalClosedCell system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair coarse ancestor) =
        ENNReal.ofReal (mass.edgeWeight coarse ancestor) := by
  have boundaryZero : xiLimitMeasure system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass
      {xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse (XiTail system coarse ancestor),
        xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse (XiHead system coarse ancestor)} = 0 := by
    change xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
      ({xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse (XiTail system coarse ancestor)} ∪
        {xiCompletionEmbedding system connected lengths lengthsPositive rate
          (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse (XiHead system coarse ancestor)}) = 0
    exact measure_union_null (noFiniteBornAtoms coarse _) (noFiniteBornAtoms coarse _)
  have boundaryPreimageZero := boundaryZero
  rw [xiLimitMeasure, Measure.map_apply
    (measurable_xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
    (by exact (isClosed_singleton.union isClosed_singleton).measurableSet)] at boundaryPreimageZero
  apply le_antisymm _
    (xiPhysicalClosedCell_mass_ge_cylinder system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass coarse ancestor)
  rw [xiLimitMeasure, Measure.map_apply
    (measurable_xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
    (xiPhysicalClosedCell_isClosed system connected lengths lengthsPositive rate rateGreaterThanOne
      eigenpair coarse ancestor).measurableSet]
  calc
    _ ≤ mass.addressMeasure
        ({address | xiAddressEdge system coarse address = ancestor} ∪
          (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) ⁻¹'
            {xiCompletionEmbedding system connected lengths lengthsPositive rate
                (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse (XiTail system coarse ancestor),
              xiCompletionEmbedding system connected lengths lengthsPositive rate
                (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse (XiHead system coarse ancestor)}) :=
      measure_mono (xiPhysicalClosedCell_preimage_subset_cylinder_union_boundary system connected
        lengths lengthsPositive rate rateGreaterThanOne eigenpair mass coarse ancestor)
    _ ≤ mass.addressMeasure {address | xiAddressEdge system coarse address = ancestor} + 0 := by
      simpa only [boundaryPreimageZero] using measure_union_le (μ := mass.addressMeasure)
        ({address | xiAddressEdge system coarse address = ancestor})
        ((xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) ⁻¹'
          {xiCompletionEmbedding system connected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse (XiTail system coarse ancestor),
            xiCompletionEmbedding system connected lengths lengthsPositive rate
              (zero_lt_one.trans rateGreaterThanOne) eigenpair coarse (XiHead system coarse ancestor)})
    _ = ENNReal.ofReal (mass.edgeWeight coarse ancestor) := by
      rw [add_zero, mass.addressMeasure_cylinder]
      rfl

theorem xiPhysicalClosedCell_mass_eq_cylinder_of_rules (system : EIGSData K)
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
    ∀ coarse (ancestor : XiEdge system.toRuleData coarse),
      xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass
        (xiPhysicalClosedCell system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair coarse ancestor) =
            ENNReal.ofReal (mass.edgeWeight coarse ancestor) := by
  intro parameters distanceGreaterThanOne mass coarse ancestor
  exact xiPhysicalClosedCell_mass_eq_cylinder system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass
    (xiFiniteBorn_singleton_mass_zero_of_rules system connected loopless unique
      plantingNonadjacent distancePositive primitiveDegree) coarse ancestor

end
end EIGS

#print axioms EIGS.xiPhysicalClosedCell_mass_eq_cylinder
#print axioms EIGS.xiPhysicalClosedCell_mass_eq_cylinder_of_rules
