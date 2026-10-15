import RequestProject.Section31.EIGSSpeedWeakLimit
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! A compact topology on the actual compatible address space. Its discrete
finite coordinates make the endpoint approximations continuous, and the
proved uniform geometric error makes the actual completion coding continuous.
This is independent of any assertion that a cadlag path space is Polish. -/

namespace EIGS
open Filter Topology ProbabilityTheory
noncomputable section
variable {K : ℕ}

instance xiPhysicalCellEdgeTopology (system : EIGSData K) (level : ℕ) :
    TopologicalSpace (XiEdge system.toRuleData level) := ⊥

instance xiPhysicalCellEdgeDiscreteTopology (system : EIGSData K) (level : ℕ) :
    DiscreteTopology (XiEdge system.toRuleData level) := ⟨rfl⟩

instance xiPhysicalCellAddressTopology (system : EIGSData K) :
    TopologicalSpace (XiEdgeAddress system) :=
  inferInstanceAs (TopologicalSpace (InverseSystem.compatiblePaths (xiEdgeParent system)))

theorem xiCompatibleAddresses_isClosed (system : EIGSData K) :
    IsClosed (InverseSystem.compatiblePaths (xiEdgeParent system)) := by
  simp only [InverseSystem.compatiblePaths, Set.setOf_forall]
  apply isClosed_iInter
  intro level
  exact isClosed_eq
    ((continuous_of_discreteTopology : Continuous (xiEdgeParent system level)).comp
      (continuous_apply (level + 1))) (continuous_apply level)

instance xiPhysicalCellAddressCompactSpace (system : EIGSData K) :
    CompactSpace (XiEdgeAddress system) :=
  isCompact_iff_compactSpace.mp (xiCompatibleAddresses_isClosed system).isCompact

theorem continuous_xiAddressEdge (system : EIGSData K) (level : ℕ) :
    Continuous (xiAddressEdge system level) :=
  (continuous_apply level).comp continuous_subtype_val

variable (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)

theorem continuous_xiAddressTailApproximation (level : ℕ) :
    Continuous (xiAddressTailApproximation system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level) :=
  (continuous_of_discreteTopology : Continuous (fun edge : XiEdge system.toRuleData level =>
    xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level (XiTail system level edge))).comp
        (continuous_xiAddressEdge system level)

theorem xiAddressTailApproximation_tendstoUniformly :
    TendstoUniformly (xiAddressTailApproximation system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair)
      (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro tolerance positive
  filter_upwards [(xiAddressError_tendsto_zero system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair).eventually (gt_mem_nhds positive)] with level small
  intro address
  rw [dist_comm]
  exact (xiAddressLimit_error system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair address level).trans_lt small

theorem continuous_xiAddressLimit :
    Continuous (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) :=
  (xiAddressTailApproximation_tendstoUniformly system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair).continuous (Filter.Eventually.of_forall
      (continuous_xiAddressTailApproximation system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)).frequently

theorem xiAddressCylinder_image_isCompact (level : ℕ) (edge : XiEdge system.toRuleData level) :
    IsCompact (xiAddressLimit system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair ''
      {address | xiAddressEdge system level address = edge}) := by
  apply IsCompact.image _ (continuous_xiAddressLimit system connected lengths lengthsPositive rate
    rateGreaterThanOne eigenpair)
  exact ((isClosed_singleton : IsClosed ({edge} : Set (XiEdge system.toRuleData level))).preimage
    (continuous_xiAddressEdge system level)).isCompact

end
end EIGS

#print axioms EIGS.xiCompatibleAddresses_isClosed
#print axioms EIGS.continuous_xiAddressLimit
#print axioms EIGS.xiAddressCylinder_image_isCompact
