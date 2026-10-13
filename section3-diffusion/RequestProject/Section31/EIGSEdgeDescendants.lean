import RequestProject.Section31.EIGSEdgeAddressMeasure
import Mathlib.Probability.Distributions.Uniform

/-! Exact counting of actual ancestor fibres. These are identities in the
defining sigma substitution, before taking any probability or asymptotic limit. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section

variable {K : ℕ}

/-- Iterating the actual first-projection parent maps. This is definitionally
the same recursion as the ancestor map used for actual harmonic cells. -/
def xiEdgeAncestor (system : EIGSData K) (initialLevel : ℕ) :
    (offset : ℕ) → XiEdge system.toRuleData (initialLevel + offset) →
      XiEdge system.toRuleData initialLevel
  | 0 => id
  | offset + 1 => fun edge => xiEdgeAncestor system initialLevel offset edge.1

theorem xiEdgeAncestor_address (system : EIGSData K) (initialLevel offset : ℕ)
    (address : XiEdgeAddress system) :
    xiEdgeAncestor system initialLevel offset
      (xiAddressEdge system (initialLevel + offset) address) =
        xiAddressEdge system initialLevel address := by
  induction offset with
  | zero => rfl
  | succ offset induction_hypothesis =>
      change xiEdgeAncestor system initialLevel offset
        (xiEdgeParent system (initialLevel + offset)
          (xiAddressEdge system (initialLevel + offset + 1) address)) = _
      rw [xiAddressEdge_parent]
      exact induction_hypothesis

/-- Any colour-weighted descendant sum in the actual graph equals the sum
in the rule system replanted at the actual ancestor colour. -/
theorem xiDescendant_weight_sum (system : EIGSData K) (initialLevel offset : ℕ)
    (ancestor : XiEdge system.toRuleData initialLevel)
    {Weights : Type*} [AddCommMonoid Weights] (weight : Fin K → Weights) :
    (∑ edge : XiEdge system.toRuleData (initialLevel + offset),
      if xiEdgeAncestor system initialLevel offset edge = ancestor then
        weight (XiCol system.toRuleData (initialLevel + offset) edge) else 0) =
      ∑ edge : XiEdge {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset,
        weight (XiCol {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor}
          offset edge) := by
  classical
  induction offset generalizing weight with
  | zero => simp [xiEdgeAncestor, XiEdge, XiCol, XiLvl]
  | succ offset induction_hypothesis =>
      change
        (∑ edge : (Σ parent : XiEdge system.toRuleData (initialLevel + offset),
          system.toRuleData.RE (XiCol system.toRuleData (initialLevel + offset) parent)),
          if xiEdgeAncestor system initialLevel offset edge.1 = ancestor then
            weight (system.toRuleData.rcol
              (XiCol system.toRuleData (initialLevel + offset) edge.1) edge.2) else 0) =
        (∑ edge : (Σ parent :
          XiEdge {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset,
          system.toRuleData.RE (XiCol
            {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset parent)),
          weight (system.toRuleData.rcol
            (XiCol {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor}
              offset edge.1) edge.2))
      rw [Fintype.sum_sigma, Fintype.sum_sigma]
      have collect_children :
          (∑ parent : XiEdge system.toRuleData (initialLevel + offset),
            ∑ child : system.toRuleData.RE (XiCol system.toRuleData (initialLevel + offset) parent),
              if xiEdgeAncestor system initialLevel offset parent = ancestor then
                weight (system.toRuleData.rcol
                  (XiCol system.toRuleData (initialLevel + offset) parent) child) else 0) =
          (∑ parent : XiEdge system.toRuleData (initialLevel + offset),
            if xiEdgeAncestor system initialLevel offset parent = ancestor then
              (∑ child : system.toRuleData.RE (XiCol system.toRuleData (initialLevel + offset) parent),
                weight (system.toRuleData.rcol
                  (XiCol system.toRuleData (initialLevel + offset) parent) child)) else 0) := by
        apply Finset.sum_congr rfl
        intro parent _
        by_cases has_ancestor : xiEdgeAncestor system initialLevel offset parent = ancestor
        · simp [has_ancestor]
        · simp [has_ancestor]
      rw [collect_children]
      exact induction_hypothesis (fun colour =>
        ∑ child : system.toRuleData.RE colour, weight (system.toRuleData.rcol colour child))

/-- The actual ancestor fibre contains exactly the replanted descendant edges. -/
theorem xiDescendant_cardinality (system : EIGSData K) (initialLevel offset : ℕ)
    (ancestor : XiEdge system.toRuleData initialLevel) :
    Fintype.card {edge : XiEdge system.toRuleData (initialLevel + offset) //
      xiEdgeAncestor system initialLevel offset edge = ancestor} =
      totalEdges {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter]
  simpa [totalEdges] using
    xiDescendant_weight_sum system initialLevel offset ancestor (fun _ => (1 : ℕ))

namespace XiMassParameters

variable {system : EIGSData K} (parameters : XiMassParameters system)

/-- The actual level edge counting measure, normalized by its actual cardinality. -/
def uniformEdgeMeasure (level : ℕ) : Measure (XiEdge system.toRuleData level) := by
  letI : Nonempty (XiEdge system.toRuleData level) := parameters.edge_nonempty level
  exact (PMF.uniformOfFintype (XiEdge system.toRuleData level)).toMeasure

instance uniformEdgeMeasure_probability (level : ℕ) :
    IsProbabilityMeasure (parameters.uniformEdgeMeasure level) := by
  unfold uniformEdgeMeasure
  infer_instance

/-- The ancestor pushforward of the actual normalized edge counting measure
has exactly the actual replanted descendant fraction at each singleton. -/
theorem uniformEdgeMeasure_ancestor_singleton (initialLevel offset : ℕ)
    (ancestor : XiEdge system.toRuleData initialLevel) :
    ((parameters.uniformEdgeMeasure (initialLevel + offset)).map
      (xiEdgeAncestor system initialLevel offset)) {ancestor} =
        (totalEdges {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor}
          offset : ℝ≥0∞) / (totalEdges system.toRuleData (initialLevel + offset) : ℝ≥0∞) := by
  classical
  letI : Nonempty (XiEdge system.toRuleData (initialLevel + offset)) :=
    parameters.edge_nonempty (initialLevel + offset)
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton ancestor)]
  change (PMF.uniformOfFintype (XiEdge system.toRuleData (initialLevel + offset))).toMeasure
    {edge | xiEdgeAncestor system initialLevel offset edge = ancestor} = _
  rw [PMF.toMeasure_uniformOfFintype_apply _ MeasurableSet.of_discrete]
  have fibre_cardinality :
      Fintype.card (↑{edge : XiEdge system.toRuleData (initialLevel + offset) |
        xiEdgeAncestor system initialLevel offset edge = ancestor}) =
      totalEdges {system.toRuleData with ι := XiCol system.toRuleData initialLevel ancestor} offset := by
    exact (Fintype.card_congr (Equiv.refl _)).trans
      (xiDescendant_cardinality system initialLevel offset ancestor)
  rw [fibre_cardinality]
  rfl

/-- The genuine actual ancestor-fibre fraction converges to its address-cylinder mass. -/
theorem actual_descendant_fraction_cylinder (initialLevel : ℕ)
    (ancestor : XiEdge system.toRuleData initialLevel) :
    Tendsto (fun offset =>
      (Fintype.card {edge : XiEdge system.toRuleData (initialLevel + offset) //
        xiEdgeAncestor system initialLevel offset edge = ancestor} : ℝ) /
      (totalEdges system.toRuleData (initialLevel + offset) : ℝ))
      atTop (𝓝 (parameters.addressMeasure
        {address | xiAddressEdge system initialLevel address = ancestor}).toReal) := by
  simpa only [xiDescendant_cardinality, Nat.add_comm initialLevel] using
    parameters.descendant_fraction_cylinder initialLevel ancestor

/-- Every actual finite ancestor marginal of the uniform edge measure
converges to the corresponding genuine infinite-address marginal. -/
theorem uniformEdgeMeasure_ancestor_mass_limit (initialLevel : ℕ)
    (ancestor : XiEdge system.toRuleData initialLevel) :
    Tendsto (fun offset =>
      (((parameters.uniformEdgeMeasure (initialLevel + offset)).map
        (xiEdgeAncestor system initialLevel offset)) {ancestor}).toReal)
      atTop (𝓝 (parameters.addressMeasure
        {address | xiAddressEdge system initialLevel address = ancestor}).toReal) := by
  simpa only [parameters.uniformEdgeMeasure_ancestor_singleton, ENNReal.toReal_div,
    ENNReal.toReal_natCast, Nat.add_comm initialLevel] using
    parameters.descendant_fraction_cylinder initialLevel ancestor

end XiMassParameters
end
end EIGS
