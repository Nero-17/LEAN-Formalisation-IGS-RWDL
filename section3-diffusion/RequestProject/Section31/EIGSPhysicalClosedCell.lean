import RequestProject.Section31.EIGSAddressGeometry
import RequestProject.Section31.EIGSCellOscillation

/-! Physical cells are closures of the embedded actual descendant vertices.
They are not defined by renaming address cylinders. The first measure bound
below follows by proving that every address through the edge converges in
that physical closed cell. The converse modulo its boundary is separate. -/

namespace EIGS
open MeasureTheory Filter Topology
noncomputable section
variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)

private theorem address_cell_ancestor (level offset : ℕ) (address : XiEdgeAddress system) :
    xiAncestorEdge system level offset (xiAddressEdge system (level + offset) address) =
      xiAddressEdge system level address := by
  induction offset with
  | zero => rfl
  | succ offset induction =>
      change xiAncestorEdge system level offset
        (xiEdgeParent system (level + offset) (xiAddressEdge system ((level + offset) + 1) address)) = _
      rw [xiAddressEdge_parent]
      exact induction

def xiPhysicalClosedCell (level : ℕ) (edge : XiEdge system.toRuleData level) :
    Set (XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
  closure (xiCompletionUnionEmbedding system connected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair '' xiDescendantCellVertices system level edge)

theorem xiPhysicalClosedCell_isClosed (level : ℕ) (edge : XiEdge system.toRuleData level) :
    IsClosed (xiPhysicalClosedCell system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level edge) := isClosed_closure

theorem xiAddressLimit_mem_physicalClosedCell (level : ℕ)
    (edge : XiEdge system.toRuleData level) (address : XiEdgeAddress system)
    (through : xiAddressEdge system level address = edge) :
    xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair address ∈
      xiPhysicalClosedCell system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair level edge := by
  have shifted : Tendsto (fun offset : ℕ => level + offset) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat level
  apply mem_closure_of_tendsto
    ((xiAddressTailApproximation_tendsto system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair address).comp shifted)
  apply Filter.Eventually.of_forall
  intro offset
  refine ⟨xiVertexEmbedding system (level + offset)
    (XiTail system (level + offset) (xiAddressEdge system (level + offset) address)), ?_, rfl⟩
  refine ⟨offset, xiAddressEdge system (level + offset) address, ?_, Or.inl rfl⟩
  exact (address_cell_ancestor system level offset address).trans through

theorem xiPhysicalClosedCell_mass_ge_cylinder (mass : XiMassParameters system)
    (level : ℕ) (edge : XiEdge system.toRuleData level) :
    ENNReal.ofReal (mass.edgeWeight level edge) ≤
      xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass
        (xiPhysicalClosedCell system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair level edge) := by
  rw [xiLimitMeasure, Measure.map_apply
    (measurable_xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
    (xiPhysicalClosedCell_isClosed system connected lengths lengthsPositive rate rateGreaterThanOne
      eigenpair level edge).measurableSet]
  dsimp only [XiMassParameters.edgeWeight]
  rw [← mass.addressMeasure_cylinder level edge]
  apply measure_mono
  intro address through
  exact xiAddressLimit_mem_physicalClosedCell system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair level edge address through

end
end EIGS

#print axioms EIGS.xiPhysicalClosedCell_isClosed
#print axioms EIGS.xiAddressLimit_mem_physicalClosedCell
#print axioms EIGS.xiPhysicalClosedCell_mass_ge_cylinder
