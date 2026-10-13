import RequestProject.Section31.EIGSVertexDescendants

/-! The paper's native uniform vertex probability and its actual completion
pushforward, together with exact coarse private-cell masses. -/

namespace EIGS

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

noncomputable section

variable {K : ℕ}

instance xiEdgeOptionMeasurableSpace (system : EIGSData K) (level : ℕ) :
    MeasurableSpace (Option (XiEdge system.toRuleData level)) := ⊤

instance xiEdgeOptionDiscreteMeasurableSpace (system : EIGSData K) (level : ℕ) :
    DiscreteMeasurableSpace (Option (XiEdge system.toRuleData level)) := ⟨fun _ => trivial⟩

private theorem xiVertexCounting_nonempty (system : EIGSData K) :
    ∀ level, Nonempty (XiVtx system level)
  | 0 => ⟨false⟩
  | level + 1 => by
    obtain ⟨vertex⟩ := xiVertexCounting_nonempty system level
    exact ⟨Sum.inl vertex⟩

def xiVertexCountingMeasure (system : EIGSData K) (level : ℕ) : Measure (XiVtx system level) := by
  letI := xiVertexCounting_nonempty system level
  exact (PMF.uniformOfFintype (XiVtx system level)).toMeasure

instance xiVertexCountingMeasure_probability (system : EIGSData K) (level : ℕ) :
    IsProbabilityMeasure (xiVertexCountingMeasure system level) := by
  unfold xiVertexCountingMeasure
  infer_instance

theorem xiVertexCountingMeasure_ancestor_singleton (system : EIGSData K) (coarseLevel offset : ℕ)
    (ancestor : XiEdge system.toRuleData coarseLevel) :
    ((xiVertexCountingMeasure system (coarseLevel + offset)).map
      (xiVertexAncestorEdge system coarseLevel offset)) {some ancestor} =
      (xiInteriorBirthCount system (XiCol system.toRuleData coarseLevel ancestor) offset : ℝ≥0∞) /
        (Fintype.card (XiVtx system (coarseLevel + offset)) : ℝ≥0∞) := by
  letI := xiVertexCounting_nonempty system (coarseLevel + offset)
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  change (PMF.uniformOfFintype (XiVtx system (coarseLevel + offset))).toMeasure
    {vertex | xiVertexAncestorEdge system coarseLevel offset vertex = some ancestor} = _
  rw [PMF.toMeasure_uniformOfFintype_apply _ MeasurableSet.of_discrete]
  have cardinality : Fintype.card
      (↑{vertex : XiVtx system (coarseLevel + offset) |
        xiVertexAncestorEdge system coarseLevel offset vertex = some ancestor}) =
        xiInteriorBirthCount system (XiCol system.toRuleData coarseLevel ancestor) offset := by
    exact (Fintype.card_congr (Equiv.refl _)).trans
      (xiVertexAncestorEdge_fibre_card system coarseLevel offset ancestor)
  rw [cardinality]

theorem xiVertexCountingMeasure_ancestor_none (system : EIGSData K) (coarseLevel offset : ℕ) :
    ((xiVertexCountingMeasure system (coarseLevel + offset)).map
      (xiVertexAncestorEdge system coarseLevel offset)) {none} =
      (Fintype.card (XiVtx system coarseLevel) : ℝ≥0∞) /
        (Fintype.card (XiVtx system (coarseLevel + offset)) : ℝ≥0∞) := by
  letI := xiVertexCounting_nonempty system (coarseLevel + offset)
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  change (PMF.uniformOfFintype (XiVtx system (coarseLevel + offset))).toMeasure
    {vertex | xiVertexAncestorEdge system coarseLevel offset vertex = none} = _
  rw [PMF.toMeasure_uniformOfFintype_apply _ MeasurableSet.of_discrete]
  have cardinality : Fintype.card
      (↑{vertex : XiVtx system (coarseLevel + offset) |
        xiVertexAncestorEdge system coarseLevel offset vertex = none}) =
        Fintype.card (XiVtx system coarseLevel) := by
    exact (Fintype.card_congr (Equiv.refl _)).trans
      (xiVertexAncestorEdge_none_card system coarseLevel offset)
  rw [cardinality]

variable (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths = rate • lengths)

def xiVertexEmpiricalMeasure (level : ℕ) :
    Measure (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
  (xiVertexCountingMeasure system level).map
    (xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level)

instance xiVertexEmpiricalMeasure_probability (level : ℕ) :
    IsProbabilityMeasure (xiVertexEmpiricalMeasure system ruleConnected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair level) :=
  Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

end
end EIGS

#print axioms EIGS.xiVertexCountingMeasure_probability
#print axioms EIGS.xiVertexCountingMeasure_ancestor_singleton
#print axioms EIGS.xiVertexCountingMeasure_ancestor_none
#print axioms EIGS.xiVertexEmpiricalMeasure_probability
