import RequestProject.Section2MetricGeometry

/-! A direct labelled-walk lift inside an actual Xi rule copy. This gives a
uniform geometric bound from every new vertex to an old vertex. -/

namespace EIGS

variable {K : ℕ}

noncomputable def xiEmbedRuleEdgeWalk (system : EIGSData K) (level : ℕ)
    (edge : XiEdge system.toRuleData level)
    {source sink : (system.ruleNetwork (XiCol system.toRuleData level edge)).V}
    (walk : (system.ruleNetwork (XiCol system.toRuleData level edge)).EdgeWalk source sink) :
    (XiNetwork system (level + 1)).EdgeWalk
      (embedRuleVtx system level edge (XiTail system level edge) (XiHead system level edge) source)
      (embedRuleVtx system level edge (XiTail system level edge) (XiHead system level edge) sink) := by
  induction walk with
  | nil => exact .nil _
  | cons ruleEdge joins rest lifted =>
    refine Network.EdgeWalk.cons (network := XiNetwork system (level + 1)) ⟨edge, ruleEdge⟩ ?_ lifted
    rcases joins with ⟨tailEquality, headEquality⟩ | ⟨tailEquality, headEquality⟩
    · exact Or.inl ⟨congrArg (embedRuleVtx system level edge _ _) tailEquality,
        congrArg (embedRuleVtx system level edge _ _) headEquality⟩
    · exact Or.inr ⟨congrArg (embedRuleVtx system level edge _ _) tailEquality,
        congrArg (embedRuleVtx system level edge _ _) headEquality⟩

theorem xiEmbedRuleEdgeWalk_cost (system : EIGSData K) (level : ℕ)
    (edge : XiEdge system.toRuleData level) (lengths : Fin K → ℝ)
    {source sink : (system.ruleNetwork (XiCol system.toRuleData level edge)).V}
    (walk : (system.ruleNetwork (XiCol system.toRuleData level edge)).EdgeWalk source sink) :
    (xiEmbedRuleEdgeWalk system level edge walk).cost lengths = walk.cost lengths := by
  induction walk with
  | nil => rfl
  | cons ruleEdge joins rest induction_hypothesis =>
    simpa only [xiEmbedRuleEdgeWalk, Network.EdgeWalk.cost, XiNetwork, XiCol, EIGSData.ruleNetwork] using
      congrArg (lengths ((system.rule _).col ruleEdge) + ·) induction_hypothesis

theorem xiWeightedDistance_rule_copy_le (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (level : ℕ) (edge : XiEdge system.toRuleData level)
    {lengths : Fin K → ℝ} (lengthsNonnegative : 0 ≤ lengths)
    (source sink : (system.ruleNetwork (XiCol system.toRuleData level edge)).V) :
    (XiNetwork system (level + 1)).weightedDistance lengths
        (embedRuleVtx system level edge (XiTail system level edge) (XiHead system level edge) source)
        (embedRuleVtx system level edge (XiTail system level edge) (XiHead system level edge) sink) ≤
      (system.ruleNetwork (XiCol system.toRuleData level edge)).weightedDistance lengths source sink := by
  letI := (system.ruleNetwork (XiCol system.toRuleData level edge)).edgeWalk_nonempty_of_connected
    (ruleConnected _) source sink
  apply le_ciInf
  intro walk
  simpa only [xiEmbedRuleEdgeWalk_cost] using
    (XiNetwork system (level + 1)).weightedDistance_le_cost lengthsNonnegative
      (xiEmbedRuleEdgeWalk system level edge walk)

def xiParentVertex (system : EIGSData K) (level : ℕ) : XiVtx system (level + 1) → XiVtx system level
  | Sum.inl oldVertex => oldVertex
  | Sum.inr ⟨edge, _⟩ => XiTail system level edge

noncomputable def xiRuleRadius (system : EIGSData K) (lengths : Fin K → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨system.initCol, system.plantPlus system.initCol⟩, Finset.mem_univ _⟩
    (fun pair : Σ colour, (system.rule colour).V =>
      (system.ruleNetwork pair.1).weightedDistance lengths (system.plantPlus pair.1) pair.2)

theorem xiRuleRadius_bound (system : EIGSData K) (lengths : Fin K → ℝ)
    (colour : Fin K) (vertex : (system.rule colour).V) :
    (system.ruleNetwork colour).weightedDistance lengths (system.plantPlus colour) vertex ≤
      xiRuleRadius system lengths := by
  unfold xiRuleRadius
  exact Finset.le_sup'
    (fun pair : Σ colour, (system.rule colour).V =>
      (system.ruleNetwork pair.1).weightedDistance lengths (system.plantPlus pair.1) pair.2)
    (Finset.mem_univ (⟨colour, vertex⟩ : Σ colour, (system.rule colour).V))

theorem xiRuleRadius_nonnegative (system : EIGSData K)
    {lengths : Fin K → ℝ} (lengthsNonnegative : 0 ≤ lengths) :
    0 ≤ xiRuleRadius system lengths := by
  simpa only [Network.weightedDistance_self _ lengthsNonnegative] using
    xiRuleRadius_bound system lengths system.initCol (system.plantPlus system.initCol)

theorem xiScaledWeightedDistance_rule_vertex_bound (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    {lengths : Fin K → ℝ} (lengthsNonnegative : 0 ≤ lengths)
    {rate : ℝ} (rateNonnegative : 0 ≤ rate) (level : ℕ) (edge : XiEdge system.toRuleData level)
    (vertex : (system.rule (XiCol system.toRuleData level edge)).V) :
    xiScaledWeightedDistance system lengths rate (level + 1)
        (Sum.inl (XiTail system level edge))
        (embedRuleVtx system level edge (XiTail system level edge) (XiHead system level edge) vertex) ≤
      rate⁻¹ ^ (level + 1) * xiRuleRadius system lengths := by
  have copyBound := xiWeightedDistance_rule_copy_le system ruleConnected level edge lengthsNonnegative
    (system.plantPlus _) vertex
  rw [embedRuleVtx_plantPlus] at copyBound
  exact mul_le_mul_of_nonneg_left (copyBound.trans (xiRuleRadius_bound system lengths _ vertex))
    (pow_nonneg (inv_nonneg.mpr rateNonnegative) _)

theorem xiScaledWeightedDistance_parent_bound (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    {lengths : Fin K → ℝ} (lengthsNonnegative : 0 ≤ lengths)
    {rate : ℝ} (rateNonnegative : 0 ≤ rate) (level : ℕ) (vertex : XiVtx system (level + 1)) :
    xiScaledWeightedDistance system lengths rate (level + 1)
        (Sum.inl (xiParentVertex system level vertex)) vertex ≤
      rate⁻¹ ^ (level + 1) * xiRuleRadius system lengths := by
  cases vertex with
  | inl oldVertex =>
    simp only [xiParentVertex, xiScaledWeightedDistance,
      Network.weightedDistance_self _ lengthsNonnegative, mul_zero]
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr rateNonnegative) _) (xiRuleRadius_nonnegative system lengthsNonnegative)
  | inr privateVertex =>
    obtain ⟨edge, vertex, notPlus, notMinus⟩ := privateVertex
    have copyBound := xiWeightedDistance_rule_copy_le system ruleConnected level edge lengthsNonnegative
      (system.plantPlus _) vertex
    have embeddedPrivate : embedRuleVtx system level edge (XiTail system level edge)
        (XiHead system level edge) vertex = Sum.inr ⟨edge, ⟨vertex, notPlus, notMinus⟩⟩ := by
      simp [embedRuleVtx, notPlus, notMinus]
    rw [embedRuleVtx_plantPlus, embeddedPrivate] at copyBound
    exact mul_le_mul_of_nonneg_left (copyBound.trans (xiRuleRadius_bound system lengths _ vertex))
      (pow_nonneg (inv_nonneg.mpr rateNonnegative) _)

end EIGS

#print axioms EIGS.xiWeightedDistance_rule_copy_le
#print axioms EIGS.xiScaledWeightedDistance_parent_bound
