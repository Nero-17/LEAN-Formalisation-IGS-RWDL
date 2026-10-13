import RequestProject.Section2MassCylinder
import RequestProject.Cluster.InverseLimit
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Probability on the actual infinite EIGS edge genealogy

The finite states are the actual `XiEdge` types, and the bonding map is the
first projection in their defining sigma recursion. Positive mass amplitudes
are constructed from the proved descendant-count limits under the original
connectedness and distance-positivity assumptions. Normalization and parent
consistency are proved from the rule-edge counts and their eigenrelation.
The infinite address measure then uses the proved Ionescu--Tulcea inverse
system construction. No metric completion or weak speed-measure limit is
asserted here.
-/

namespace EIGS

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section

variable {K : ℕ}

structure XiMassParameters (system : EIGSData K) where
  rate : ℝ
  amplitude : Fin K → ℝ
  rate_positive : 0 < rate
  amplitude_positive : ∀ colour, 0 < amplitude colour
  eigenpair : (massMatrixR system.toRuleData).mulVec amplitude = rate • amplitude
  descendant_fraction_converges : ∀ cellLevel cellColour,
    Tendsto (fun level =>
      (totalEdges { system.toRuleData with ι := cellColour } level : ℝ) /
        (totalEdges system.toRuleData (level + cellLevel) : ℝ))
      atTop (𝓝 (amplitude cellColour / (rate ^ cellLevel * amplitude system.initCol)))

/-- The parameters are selected from proved actual descendant-count asymptotics. -/
def xiMassParametersOfRules (system : EIGSData K)
    (rules_connected : ∀ colour, (ruleSG system colour).Connected)
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    XiMassParameters system :=
  Classical.choice (show Nonempty (XiMassParameters system) from by
    obtain ⟨rate, amplitude, rate_positive, amplitude_positive, eigenpair, convergence⟩ :=
      eigs_descendant_fraction_limits system rules_connected distance_positive
    exact ⟨⟨rate, amplitude, rate_positive, amplitude_positive, eigenpair, convergence⟩⟩)

instance xiEdgeMeasurableSpace (system : EIGSData K) (level : ℕ) :
    MeasurableSpace (XiEdge system.toRuleData level) := ⊤

instance xiEdgeDiscreteMeasurableSpace (system : EIGSData K) (level : ℕ) :
    DiscreteMeasurableSpace (XiEdge system.toRuleData level) := ⟨fun _ => trivial⟩

/-- Actual substitution forgets the final rule edge by the defining first projection. -/
def xiEdgeParent (system : EIGSData K) (level : ℕ) :
    XiEdge system.toRuleData (level + 1) → XiEdge system.toRuleData level := fun edge => edge.1

theorem xiEdgeParent_mk (system : EIGSData K) (level : ℕ)
    (parent : XiEdge system.toRuleData level)
    (child : (system.rule (XiCol system.toRuleData level parent)).E) :
    xiEdgeParent system level ⟨parent, child⟩ = parent := rfl

namespace XiMassParameters

variable {system : EIGSData K} (parameters : XiMassParameters system)

theorem sum_rule_amplitudes (colour : Fin K) :
    (∑ edge : (system.rule colour).E, parameters.amplitude ((system.rule colour).col edge)) =
      parameters.rate * parameters.amplitude colour := by
  have count_identity :
      (∑ edge : (system.rule colour).E, parameters.amplitude ((system.rule colour).col edge)) =
        (massMatrixR system.toRuleData).mulVec parameters.amplitude colour := by
    classical
    simp only [Matrix.mulVec, dotProduct, massMatrixR, massMatrix, EIGSData.toRuleData,
      Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro edge _
    simp
  rw [count_identity, parameters.eigenpair]
  rfl

theorem sum_edge_amplitudes (level : ℕ) :
    (∑ edge : XiEdge system.toRuleData level,
      parameters.amplitude (XiCol system.toRuleData level edge)) =
        parameters.rate ^ level * parameters.amplitude system.initCol := by
  induction level with
  | zero => simp [XiEdge, XiCol, XiLvl, EIGSData.toRuleData]
  | succ level induction_hypothesis =>
      change (∑ edge : (Σ parent : XiEdge system.toRuleData level,
        (system.rule (XiCol system.toRuleData level parent)).E),
          parameters.amplitude ((system.rule (XiCol system.toRuleData level edge.1)).col edge.2)) = _
      rw [Fintype.sum_sigma]
      simp_rw [parameters.sum_rule_amplitudes]
      rw [← Finset.mul_sum, induction_hypothesis, pow_succ]
      ring

def edgeWeight (level : ℕ) (edge : XiEdge system.toRuleData level) : ℝ :=
  parameters.amplitude (XiCol system.toRuleData level edge) /
    (parameters.rate ^ level * parameters.amplitude system.initCol)

theorem edgeWeight_positive (level : ℕ) (edge : XiEdge system.toRuleData level) :
    0 < parameters.edgeWeight level edge :=
  div_pos (parameters.amplitude_positive _)
    (mul_pos (pow_pos parameters.rate_positive level) (parameters.amplitude_positive _))

theorem sum_edgeWeight (level : ℕ) :
    (∑ edge : XiEdge system.toRuleData level, parameters.edgeWeight level edge) = 1 := by
  simp only [edgeWeight, ← Finset.sum_div, parameters.sum_edge_amplitudes]
  exact div_self (mul_pos (pow_pos parameters.rate_positive level)
    (parameters.amplitude_positive _)).ne'

theorem sum_child_edgeWeight (level : ℕ) (parent : XiEdge system.toRuleData level) :
    (∑ child : (system.rule (XiCol system.toRuleData level parent)).E,
      parameters.edgeWeight (level + 1) ⟨parent, child⟩) = parameters.edgeWeight level parent := by
  change (∑ child : (system.rule (XiCol system.toRuleData level parent)).E,
    parameters.amplitude ((system.rule (XiCol system.toRuleData level parent)).col child) /
      (parameters.rate ^ (level + 1) * parameters.amplitude system.initCol)) = _
  rw [← Finset.sum_div, parameters.sum_rule_amplitudes]
  simp only [edgeWeight, pow_succ]
  field_simp [parameters.rate_positive.ne', (parameters.amplitude_positive system.initCol).ne']

def edgePMF (level : ℕ) : PMF (XiEdge system.toRuleData level) :=
  PMF.ofFintype (fun edge => ENNReal.ofReal (parameters.edgeWeight level edge)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun edge _ => (parameters.edgeWeight_positive level edge).le), parameters.sum_edgeWeight]
    simp)

@[simp] theorem edgePMF_apply (level : ℕ) (edge : XiEdge system.toRuleData level) :
    parameters.edgePMF level edge = ENNReal.ofReal (parameters.edgeWeight level edge) := rfl

theorem edgePMF_parent (level : ℕ) :
    (parameters.edgePMF (level + 1)).map (xiEdgeParent system level) =
      parameters.edgePMF level := by
  classical
  ext parent
  rw [PMF.map_apply, tsum_fintype]
  simp only [parameters.edgePMF_apply, xiEdgeParent]
  change (∑ edge : (Σ parent : XiEdge system.toRuleData level,
    (system.rule (XiCol system.toRuleData level parent)).E),
      if parent = edge.1 then ENNReal.ofReal (parameters.edgeWeight (level + 1) edge) else 0) =
        ENNReal.ofReal (parameters.edgeWeight level parent)
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single parent]
  · simp only [ite_true]
    calc
      _ = ENNReal.ofReal (∑ child : (system.rule (XiCol system.toRuleData level parent)).E,
          parameters.edgeWeight (level + 1) ⟨parent, child⟩) :=
        (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
          (f := fun child : (system.rule (XiCol system.toRuleData level parent)).E =>
            parameters.edgeWeight (level + 1) ⟨parent, child⟩)
          (fun child _ => (parameters.edgeWeight_positive (level + 1) ⟨parent, child⟩).le)).symm
      _ = _ := congrArg ENNReal.ofReal (parameters.sum_child_edgeWeight level parent)
  · intro other _ other_ne
    simp [Ne.symm other_ne]
  · simp

def edgeLaw (level : ℕ) : Measure (XiEdge system.toRuleData level) :=
  (parameters.edgePMF level).toMeasure

instance edgeLaw_probability (level : ℕ) : IsProbabilityMeasure (parameters.edgeLaw level) := by
  unfold edgeLaw
  infer_instance

theorem edgeLaw_parent (level : ℕ) :
    (parameters.edgeLaw (level + 1)).map (xiEdgeParent system level) =
      parameters.edgeLaw level := by
  rw [edgeLaw, PMF.toMeasure_map (xiEdgeParent system level)
    (parameters.edgePMF (level + 1)) Measurable.of_discrete, parameters.edgePMF_parent]
  rfl

include parameters in
theorem edge_nonempty (level : ℕ) : Nonempty (XiEdge system.toRuleData level) := by
  obtain ⟨edge, _⟩ := (parameters.edgePMF level).support_nonempty
  exact ⟨edge⟩

end XiMassParameters

/-- An actual infinite address is a compatible ancestral chain of actual substitution edges. -/
def XiEdgeAddress (system : EIGSData K) :=
  InverseSystem.compatiblePaths (xiEdgeParent system)

instance xiEdgeAddressMeasurableSpace (system : EIGSData K) :
    MeasurableSpace (XiEdgeAddress system) :=
  inferInstanceAs (MeasurableSpace (InverseSystem.compatiblePaths (xiEdgeParent system)))

def xiAddressEdge (system : EIGSData K) (level : ℕ) (address : XiEdgeAddress system) :
    XiEdge system.toRuleData level := address.val level

theorem measurable_xiAddressEdge (system : EIGSData K) (level : ℕ) :
    Measurable (xiAddressEdge system level) :=
  (measurable_pi_apply level).comp measurable_subtype_coe

theorem xiAddressEdge_parent (system : EIGSData K) (address : XiEdgeAddress system) (level : ℕ) :
    xiEdgeParent system level (xiAddressEdge system (level + 1) address) =
      xiAddressEdge system level address := address.property level

/-- Equality at a later actual edge forces equality of every preceding edge. -/
theorem xiAddressEdge_initial_agreement (system : EIGSData K) (upperLevel : ℕ) :
    ∀ first second : XiEdgeAddress system,
      xiAddressEdge system upperLevel first = xiAddressEdge system upperLevel second →
      ∀ level, level ≤ upperLevel →
        xiAddressEdge system level first = xiAddressEdge system level second := by
  induction upperLevel with
  | zero =>
      intro first second agreement level bound
      have level_zero : level = 0 := Nat.eq_zero_of_le_zero bound
      subst level
      exact agreement
  | succ upperLevel induction_hypothesis =>
      intro first second agreement level bound
      by_cases level_last : level = upperLevel + 1
      · subst level
        exact agreement
      · have parent_agreement := congrArg (xiEdgeParent system upperLevel) agreement
        rw [xiAddressEdge_parent, xiAddressEdge_parent] at parent_agreement
        exact induction_hypothesis first second parent_agreement level (by omega)

theorem xiAddressEdge_eq_of_prefix_compatible (system : EIGSData K) (upperLevel : ℕ)
    (edges : (level : ℕ) → XiEdge system.toRuleData level) :
    (∀ level, level < upperLevel → xiEdgeParent system level (edges (level + 1)) = edges level) →
    ∀ address : XiEdgeAddress system,
      xiAddressEdge system upperLevel address = edges upperLevel →
      ∀ level, level ≤ upperLevel → xiAddressEdge system level address = edges level := by
  induction upperLevel with
  | zero =>
      intro _ address agreement level bound
      have level_zero : level = 0 := Nat.eq_zero_of_le_zero bound
      subst level
      exact agreement
  | succ upperLevel induction_hypothesis =>
      intro compatible address agreement level bound
      by_cases level_last : level = upperLevel + 1
      · subst level
        exact agreement
      · have parent_agreement := congrArg (xiEdgeParent system upperLevel) agreement
        rw [xiAddressEdge_parent, compatible upperLevel (Nat.lt_succ_self upperLevel)]
          at parent_agreement
        exact induction_hypothesis
          (fun previousLevel previous_bound => compatible previousLevel (by omega))
          address parent_agreement level (by omega)

namespace XiMassParameters

variable {system : EIGSData K} (parameters : XiMassParameters system)

def addressMeasure : Measure (XiEdgeAddress system) := by
  letI : ∀ level, Nonempty (XiEdge system.toRuleData level) := parameters.edge_nonempty
  exact InverseSystem.compatibleMeasure parameters.edgeLaw (xiEdgeParent system)

instance addressMeasure_probability : IsProbabilityMeasure parameters.addressMeasure := by
  letI : ∀ level, Nonempty (XiEdge system.toRuleData level) := parameters.edge_nonempty
  exact InverseSystem.compatibleMeasure_probability parameters.edgeLaw (xiEdgeParent system)
    (fun _ => Measurable.of_discrete) parameters.edgeLaw_parent

theorem addressMeasure_coordinate (level : ℕ) :
    parameters.addressMeasure.map (xiAddressEdge system level) = parameters.edgeLaw level := by
  letI : ∀ level, Nonempty (XiEdge system.toRuleData level) := parameters.edge_nonempty
  exact InverseSystem.compatibleMeasure_map_eval parameters.edgeLaw (xiEdgeParent system)
    (fun _ => Measurable.of_discrete) parameters.edgeLaw_parent level

theorem addressMeasure_cylinder (level : ℕ) (edge : XiEdge system.toRuleData level) :
    parameters.addressMeasure {address | xiAddressEdge system level address = edge} =
      ENNReal.ofReal (parameters.amplitude (XiCol system.toRuleData level edge) /
        (parameters.rate ^ level * parameters.amplitude system.initCol)) := by
  have singleton_law := congrArg (fun probability => probability ({edge} : Set _))
    (parameters.addressMeasure_coordinate level)
  dsimp only at singleton_law
  rw [Measure.map_apply (measurable_xiAddressEdge system level) (measurableSet_singleton edge)]
    at singleton_law
  simpa only [edgeLaw, parameters.edgePMF_apply, edgeWeight] using
    singleton_law.trans ((parameters.edgePMF level).toMeasure_apply_singleton edge
      (measurableSet_singleton edge))

/-- Every finite compatible initial cylinder is determined by its last actual edge. -/
theorem addressMeasure_prefix_cylinder (upperLevel : ℕ) (reference : XiEdgeAddress system) :
    parameters.addressMeasure
      {address | ∀ level, level ≤ upperLevel →
        xiAddressEdge system level address = xiAddressEdge system level reference} =
      ENNReal.ofReal (parameters.edgeWeight upperLevel
        (xiAddressEdge system upperLevel reference)) := by
  have cylinder_identity :
      {address : XiEdgeAddress system | ∀ level, level ≤ upperLevel →
        xiAddressEdge system level address = xiAddressEdge system level reference} =
      {address | xiAddressEdge system upperLevel address =
        xiAddressEdge system upperLevel reference} := by
    ext address
    exact ⟨fun agreement => agreement upperLevel le_rfl,
      fun agreement => xiAddressEdge_initial_agreement system upperLevel address reference agreement⟩
  rw [cylinder_identity, parameters.addressMeasure_cylinder]
  rfl

/-- All finite initial cylinders, including inconsistent specifications, have their exact mass. -/
theorem addressMeasure_initial_cylinder (upperLevel : ℕ)
    (edges : (level : ℕ) → XiEdge system.toRuleData level) :
    parameters.addressMeasure
      {address | ∀ level, level ≤ upperLevel → xiAddressEdge system level address = edges level} =
      if (∀ level, level < upperLevel →
        xiEdgeParent system level (edges (level + 1)) = edges level) then
        ENNReal.ofReal (parameters.edgeWeight upperLevel (edges upperLevel)) else 0 := by
  classical
  split_ifs with compatible
  · have cylinder_identity :
        {address : XiEdgeAddress system | ∀ level, level ≤ upperLevel →
          xiAddressEdge system level address = edges level} =
        {address | xiAddressEdge system upperLevel address = edges upperLevel} := by
      ext address
      exact ⟨fun agreement => agreement upperLevel le_rfl,
        fun agreement => xiAddressEdge_eq_of_prefix_compatible system upperLevel edges
          compatible address agreement⟩
    rw [cylinder_identity, parameters.addressMeasure_cylinder]
    rfl
  · have empty_cylinder :
        {address : XiEdgeAddress system | ∀ level, level ≤ upperLevel →
          xiAddressEdge system level address = edges level} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro address agreement
      apply compatible
      intro level bound
      have next_bound : level + 1 ≤ upperLevel := Nat.succ_le_iff.mpr bound
      calc
        xiEdgeParent system level (edges (level + 1)) =
            xiEdgeParent system level (xiAddressEdge system (level + 1) address) :=
          congrArg (xiEdgeParent system level) (agreement (level + 1) next_bound).symm
        _ = xiAddressEdge system level address := xiAddressEdge_parent system address level
        _ = edges level := agreement level (by omega)
    rw [empty_cylinder, measure_empty]

include parameters in
/-- No actual edge is discarded by the infinite compatible-address construction. -/
theorem exists_address_through_edge (level : ℕ) (edge : XiEdge system.toRuleData level) :
    ∃ address : XiEdgeAddress system, xiAddressEdge system level address = edge := by
  classical
  by_contra no_address
  have empty_cylinder : {address | xiAddressEdge system level address = edge} =
      (∅ : Set (XiEdgeAddress system)) := by
    ext address
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun agreement => no_address ⟨address, agreement⟩
  have cylinder_positive : 0 < parameters.addressMeasure
      {address | xiAddressEdge system level address = edge} := by
    rw [parameters.addressMeasure_cylinder]
    exact ENNReal.ofReal_pos.mpr (parameters.edgeWeight_positive level edge)
  rw [empty_cylinder, measure_empty] at cylinder_positive
  exact (lt_irrefl 0) cylinder_positive

/-- The cylinder formula agrees with the proved actual descendant-count fraction limit. -/
theorem descendant_fraction_cylinder (level : ℕ) (edge : XiEdge system.toRuleData level) :
    Tendsto (fun depth =>
      (totalEdges { system.toRuleData with ι := XiCol system.toRuleData level edge } depth : ℝ) /
        (totalEdges system.toRuleData (depth + level) : ℝ))
      atTop (𝓝 (parameters.addressMeasure
        {address | xiAddressEdge system level address = edge}).toReal) := by
  have weight_nonnegative : 0 ≤ parameters.amplitude (XiCol system.toRuleData level edge) /
      (parameters.rate ^ level * parameters.amplitude system.initCol) :=
    (parameters.edgeWeight_positive level edge).le
  rw [parameters.addressMeasure_cylinder, ENNReal.toReal_ofReal weight_nonnegative]
  exact parameters.descendant_fraction_converges level (XiCol system.toRuleData level edge)

end XiMassParameters
end
end EIGS
