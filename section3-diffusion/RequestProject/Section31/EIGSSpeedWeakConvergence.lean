import RequestProject.Section31.EIGSAddressMeasure
import RequestProject.Section31.EIGSEdgeMarginals
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Native finite-vertex speed probabilities and their actual completion image. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section

variable {K : ℕ}

instance xiVertexMeasurableSpace (system : EIGSData K) (level : ℕ) :
    MeasurableSpace (XiVtx system level) := ⊤

instance xiVertexDiscreteMeasurableSpace (system : EIGSData K) (level : ℕ) :
    DiscreteMeasurableSpace (XiVtx system level) := ⟨fun _ => trivial⟩

/-- The native finite speed law is the uniform actual edge's two endpoint laws. -/
def xiVertexSpeedMeasure (system : EIGSData K) (mass : XiMassParameters system) (level : ℕ) :
    Measure (XiVtx system level) :=
  (1 / 2 : ℝ≥0∞) • (mass.uniformEdgeMeasure level).map (XiTail system level) +
    (1 / 2 : ℝ≥0∞) • (mass.uniformEdgeMeasure level).map (XiHead system level)

instance xiVertexSpeedMeasure_probability (system : EIGSData K)
    (mass : XiMassParameters system) (level : ℕ) :
    IsProbabilityMeasure (xiVertexSpeedMeasure system mass level) where
  measure_univ := by
    simp [xiVertexSpeedMeasure, Measure.add_apply, Measure.smul_apply,
      Measure.map_apply Measurable.of_discrete, ENNReal.inv_two_add_inv_two]

/-- The incidence degree counts the two actual endpoint fibres. -/
def xiVertexIncidenceCount (system : EIGSData K) (level : ℕ) (vertex : XiVtx system level) : ℕ :=
  Nat.card {edge : XiEdge system.toRuleData level // XiTail system level edge = vertex} +
    Nat.card {edge : XiEdge system.toRuleData level // XiHead system level edge = vertex}

theorem uniformEdgeMeasure_endpoint_singleton (system : EIGSData K)
    (mass : XiMassParameters system) (level : ℕ)
    (endpoint : XiEdge system.toRuleData level → XiVtx system level) (vertex : XiVtx system level) :
    ((mass.uniformEdgeMeasure level).map endpoint) {vertex} =
      (Nat.card {edge : XiEdge system.toRuleData level // endpoint edge = vertex} : ℝ≥0∞) /
        (totalEdges system.toRuleData level : ℝ≥0∞) := by
  classical
  letI : Nonempty (XiEdge system.toRuleData level) := mass.edge_nonempty level
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton vertex)]
  change (PMF.uniformOfFintype (XiEdge system.toRuleData level)).toMeasure
    {edge | endpoint edge = vertex} = _
  rw [PMF.toMeasure_uniformOfFintype_apply _ MeasurableSet.of_discrete,
    ← Nat.card_eq_fintype_card]
  rfl

theorem xiVertexSpeedMeasure_singleton (system : EIGSData K)
    (mass : XiMassParameters system) (level : ℕ) (vertex : XiVtx system level) :
    xiVertexSpeedMeasure system mass level {vertex} =
      (xiVertexIncidenceCount system level vertex : ℝ≥0∞) /
        (2 * (totalEdges system.toRuleData level : ℝ≥0∞)) := by
  rw [xiVertexSpeedMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    uniformEdgeMeasure_endpoint_singleton, uniformEdgeMeasure_endpoint_singleton]
  simp only [smul_eq_mul, xiVertexIncidenceCount, Nat.cast_add, div_eq_mul_inv, one_mul]
  rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  ring

variable (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths = rate • lengths)

theorem xiVertexSpeedMeasure_map (mass : XiMassParameters system) (level : ℕ) :
    (xiVertexSpeedMeasure system mass level).map
      (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level) =
      xiSpeedMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level := by
  rw [xiVertexSpeedMeasure, xiSpeedMeasure,
    Measure.map_add _ _ Measurable.of_discrete, Measure.map_smul, Measure.map_smul,
    Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  rfl

end
end EIGS
