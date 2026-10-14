import RequestProject.Section2WeightedSubstitution

/-! A metric-potential extension which keeps selected copies constant.
The selected parent edges must have equal endpoint values. This is the
one-step ingredient for separating a whole current cell from the complement
of its two endpoint stars; the iterated actual-cell consumer remains to be
proved. Candidate source: no compilation is claimed. -/

namespace EIGS.Network
open scoped Classical
noncomputable section
variable {K : ℕ} (network : Network K) (rules : RuleFamily K)

def substSelectedFlatMetricPotential (lengths : Fin K → ℝ)
    (potential : network.V → ℝ) (flat : network.E → Prop) : (network.subst rules).V → ℝ
  | Sum.inl vertex => potential vertex
  | Sum.inr ⟨edge, interior⟩ =>
      if flat edge then potential (network.tail edge)
      else network.substMetricPotential rules lengths potential (Sum.inr ⟨edge, interior⟩)

theorem substSelectedFlatMetricPotential_on_copy (lengths : Fin K → ℝ)
    (potential : network.V → ℝ) (flat : network.E → Prop)
    (flatEndpoints : ∀ edge, flat edge → potential (network.tail edge) = potential (network.head edge))
    (edge : network.E) (vertex : (rules.R (network.color edge)).V) :
    network.substSelectedFlatMetricPotential rules lengths potential flat
      (network.substEmbed rules edge vertex) =
      if flat edge then potential (network.tail edge)
      else network.substMetricPotential rules lengths potential (network.substEmbed rules edge vertex) := by
  by_cases selected : flat edge
  · rw [if_pos selected]
    by_cases plusEquality : vertex = rules.βplus (network.color edge)
    · subst vertex
      rw [substEmbed_plantPlus]
      rfl
    · by_cases minusEquality : vertex = rules.βminus (network.color edge)
      · subst vertex
        rw [substEmbed_plantMinus]
        exact (flatEndpoints edge selected).symm
      · simp only [substEmbed, plusEquality, minusEquality, ↓reduceDIte,
          substSelectedFlatMetricPotential, if_pos selected]
  · rw [if_neg selected]
    by_cases plusEquality : vertex = rules.βplus (network.color edge)
    · subst vertex
      rw [substEmbed_plantPlus]
      rfl
    · by_cases minusEquality : vertex = rules.βminus (network.color edge)
      · subst vertex
        rw [substEmbed_plantMinus]
        rfl
      · simp only [substEmbed, plusEquality, minusEquality, ↓reduceDIte,
          substSelectedFlatMetricPotential, if_neg selected]

theorem substSelectedFlatMetricPotential_lipschitz
    (rulesConnected : ∀ colour, (rules.R colour).toSimpleGraph.Connected)
    {lengths : Fin K → ℝ} (lengthsNonnegative : 0 ≤ lengths)
    (potential : network.V → ℝ) (flat : network.E → Prop)
    (flatEndpoints : ∀ edge, flat edge → potential (network.tail edge) = potential (network.head edge))
    (lipschitz : network.EdgeLipschitz (rules.metricLengths lengths) potential) :
    (network.subst rules).EdgeLipschitz lengths
      (network.substSelectedFlatMetricPotential rules lengths potential flat) := by
  have standard := network.substMetricPotential_lipschitz rules rulesConnected
    lengthsNonnegative potential lipschitz
  intro edge
  change |network.substSelectedFlatMetricPotential rules lengths potential flat
      (network.substEmbed rules edge.1 ((rules.R (network.color edge.1)).tail edge.2)) -
    network.substSelectedFlatMetricPotential rules lengths potential flat
      (network.substEmbed rules edge.1 ((rules.R (network.color edge.1)).head edge.2))| ≤ _
  rw [network.substSelectedFlatMetricPotential_on_copy rules lengths potential flat flatEndpoints,
    network.substSelectedFlatMetricPotential_on_copy rules lengths potential flat flatEndpoints]
  by_cases selected : flat edge.1
  · simp only [if_pos selected, sub_self, abs_zero]
    exact lengthsNonnegative _
  · simp only [if_neg selected]
    exact standard edge

theorem substSelectedFlatMetricPotential_constant_on_selected_copy
    (lengths : Fin K → ℝ) (potential : network.V → ℝ) (flat : network.E → Prop)
    (flatEndpoints : ∀ edge, flat edge → potential (network.tail edge) = potential (network.head edge))
    (edge : network.E) (selected : flat edge) (vertex : (rules.R (network.color edge)).V) :
    network.substSelectedFlatMetricPotential rules lengths potential flat
      (network.substEmbed rules edge vertex) = potential (network.tail edge) := by
  rw [network.substSelectedFlatMetricPotential_on_copy rules lengths potential flat flatEndpoints,
    if_pos selected]

end
end EIGS.Network

#print axioms EIGS.Network.substSelectedFlatMetricPotential_on_copy
#print axioms EIGS.Network.substSelectedFlatMetricPotential_lipschitz
#print axioms EIGS.Network.substSelectedFlatMetricPotential_constant_on_selected_copy
