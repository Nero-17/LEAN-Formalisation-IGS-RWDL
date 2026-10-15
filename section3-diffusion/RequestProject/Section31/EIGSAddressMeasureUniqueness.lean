import RequestProject.Section31.EIGSEdgeAddressMeasure
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! Compatible actual edge addresses have their full law determined by
their single-level marginals: every earlier edge is an ancestor of the
last edge. This is not an independence assertion about edge coordinates. -/

namespace EIGS
open MeasureTheory ProbabilityTheory Preorder Finset
noncomputable section
set_option maxHeartbeats 3000000

theorem xiAddressMeasure_eq_of_marginals {K : ℕ} (system : EIGSData K)
    (first second : Measure (XiEdgeAddress system)) [IsFiniteMeasure second]
    (marginals : ∀ level,
      first.map (xiAddressEdge system level) = second.map (xiAddressEdge system level)) :
    first = second := by
  classical
  rcases isEmpty_or_nonempty (XiEdgeAddress system) with empty | nonempty
  · letI := empty
    exact Subsingleton.elim _ _
  letI := nonempty
  letI : ∀ level, Nonempty (XiEdge system.toRuleData level) := fun level =>
    ⟨xiAddressEdge system level (Classical.choice nonempty)⟩
  have prefixLaws (level : ℕ) :
      (first.map Subtype.val).map (frestrictLe level) =
        (second.map Subtype.val).map (frestrictLe level) := by
    let prefixFromLast : XiEdge system.toRuleData level →
        ((index : Finset.Iic level) → XiEdge system.toRuleData index.val) := fun edge =>
      if witness : ∃ address : XiEdgeAddress system, xiAddressEdge system level address = edge then
        frestrictLe level (Classical.choose witness).val
      else frestrictLe level (Classical.choice nonempty).val
    have factors : (fun address : XiEdgeAddress system => frestrictLe level address.val) =
        prefixFromLast ∘ xiAddressEdge system level := by
      funext address
      dsimp only [Function.comp_def, prefixFromLast]
      rw [dif_pos (show ∃ other : XiEdgeAddress system,
        xiAddressEdge system level other = xiAddressEdge system level address from ⟨address, rfl⟩)]
      funext index
      exact (xiAddressEdge_initial_agreement system level _ _
        (Classical.choose_spec (show ∃ other : XiEdgeAddress system,
          xiAddressEdge system level other = xiAddressEdge system level address from ⟨address, rfl⟩))
        index.val (Finset.mem_Iic.mp index.property)).symm
    rw [Measure.map_map (measurable_frestrictLe _) measurable_subtype_coe,
      Measure.map_map (measurable_frestrictLe _) measurable_subtype_coe]
    change first.map (fun address => frestrictLe level address.val) =
      second.map (fun address => frestrictLe level address.val)
    rw [factors, ← Measure.map_map (Measurable.of_discrete : Measurable prefixFromLast)
      (measurable_xiAddressEdge system level), marginals,
      Measure.map_map (Measurable.of_discrete : Measurable prefixFromLast)
        (measurable_xiAddressEdge system level)]
  let secondPaths : Measure ((level : ℕ) → XiEdge system.toRuleData level) :=
    second.map Subtype.val
  let family : (indices : Finset ℕ) →
      Measure ((index : indices) → XiEdge system.toRuleData index.val) :=
    fun indices => secondPaths.map indices.restrict
  have projective : IsProjectiveMeasureFamily family :=
    isProjectiveMeasureFamily_map_restrict (P := secondPaths)
      (X := fun level path => path level) (fun _ => (measurable_pi_apply _).aemeasurable)
  haveI : ∀ indices, IsFiniteMeasure (family indices) := fun _ => by
    dsimp [family, secondPaths]
    infer_instance
  have firstProjective : IsProjectiveLimit (first.map Subtype.val) family := by
    apply (isProjectiveLimit_nat_iff projective (first.map Subtype.val)).mpr
    exact prefixLaws
  have secondProjective : IsProjectiveLimit secondPaths family := fun _ => rfl
  have pathsEqual := firstProjective.unique secondProjective
  exact (MeasurableEmbedding.subtype_coe
    (InverseSystem.measurableSet_compatiblePaths (xiEdgeParent system)
      (fun _ => Measurable.of_discrete))).map_injective pathsEqual

end
end EIGS

#print axioms EIGS.xiAddressMeasure_eq_of_marginals
