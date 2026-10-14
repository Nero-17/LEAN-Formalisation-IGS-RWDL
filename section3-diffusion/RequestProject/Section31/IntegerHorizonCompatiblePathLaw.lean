import RequestProject.Section31.DependentCoherentPrefixPathLaw
import RequestProject.Section31.IntegerHorizonPathReconstruction
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Compatible continuous integer-horizon probabilities are extended to one
probability on continuous nonnegative-real-time paths. All finite evaluation
laws are recovered exactly. This uses genuine dependent Ionescu--Tulcea
extension and a measurable reconstruction, with the evaluation sigma algebra. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology Preorder
open scoped UniformConvergence NNReal Classical
noncomputable section
set_option maxHeartbeats 5000000

variable {State : Type*} [MetricSpace State] [CompactSpace State] [Nonempty State]
variable [MeasurableSpace State] [BorelSpace State]
variable {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]
local instance : ∀ level, MeasurableSpace (Vertex level) := fun _ => ⊤

variable (rates : ℕ → ℝ≥0) (embedding : (level : ℕ) → Vertex level → State)

def integerHorizonPrefix (horizon : ℕ)
    (path : FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding))
    (index : Finset.Iic horizon) :
    FiniteSupportPathSpace (finiteHorizonStepPaths (index.val : ℝ≥0) rates embedding) :=
  finiteHorizonPathRestriction (index.val : ℝ≥0) (horizon : ℝ≥0)
    (by exact_mod_cast Finset.mem_Iic.mp index.property) rates embedding path

theorem integerHorizonPrefix_measurable (horizon : ℕ) :
    Measurable (integerHorizonPrefix rates embedding horizon) := by
  apply measurable_pi_lambda
  intro index
  exact (finiteHorizonPathRestriction_continuous (index.val : ℝ≥0) (horizon : ℝ≥0)
    (by exact_mod_cast Finset.mem_Iic.mp index.property) rates embedding).measurable

theorem integerHorizonPrefix_last (horizon : ℕ)
    (path : FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding)) :
    integerHorizonPrefix rates embedding horizon path ⟨horizon, Finset.mem_Iic.mpr le_rfl⟩ = path := by
  apply Subtype.ext
  rfl

theorem integerHorizonPrefix_comp_restriction (shortHorizon longHorizon : ℕ)
    (ordered : shortHorizon ≤ longHorizon)
    (path : FiniteSupportPathSpace (finiteHorizonStepPaths (longHorizon : ℝ≥0) rates embedding))
    (index : Finset.Iic shortHorizon) :
    integerHorizonPrefix rates embedding shortHorizon
      (finiteHorizonPathRestriction (shortHorizon : ℝ≥0) (longHorizon : ℝ≥0)
        (by exact_mod_cast ordered) rates embedding path) index =
      integerHorizonPrefix rates embedding longHorizon path
        ⟨index.val, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp index.property).trans ordered)⟩ := by
  apply Subtype.ext
  rfl

variable (laws : (horizon : ℕ) →
  ProbabilityMeasure (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding)))

def integerHorizonPrefixLaws (horizon : ℕ) :
    Measure ((index : Finset.Iic horizon) →
      FiniteSupportPathSpace (finiteHorizonStepPaths (index.val : ℝ≥0) rates embedding)) :=
  (laws horizon : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding))).map (integerHorizonPrefix rates embedding horizon)

instance integerHorizonPrefixLaws_isProbability (horizon : ℕ) :
    IsProbabilityMeasure (integerHorizonPrefixLaws rates embedding laws horizon) :=
  Measure.isProbabilityMeasure_map (integerHorizonPrefix_measurable rates embedding horizon).aemeasurable

variable (compatible : ∀ (shortHorizon longHorizon : ℕ) (ordered : shortHorizon ≤ longHorizon),
  (laws longHorizon).map
    (finiteHorizonPathRestriction_continuous (shortHorizon : ℝ≥0) (longHorizon : ℝ≥0)
      (by exact_mod_cast ordered) rates embedding).measurable.aemeasurable = laws shortHorizon)

include compatible in
theorem integerHorizonPrefixLaws_coherent (horizon : ℕ) :
    (integerHorizonPrefixLaws rates embedding laws (horizon + 1)).map
      (frestrictLe₂ (π := fun index : ℕ =>
        FiniteSupportPathSpace (finiteHorizonStepPaths (index : ℝ≥0) rates embedding)) (Nat.le_succ horizon)) =
      integerHorizonPrefixLaws rates embedding laws horizon := by
  have compatibleMeasures := congrArg (fun law : ProbabilityMeasure
    (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding)) =>
      (law : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding)))) (compatible horizon (horizon + 1) (Nat.le_succ horizon))
  change (laws (horizon + 1) : Measure
    (FiniteSupportPathSpace (finiteHorizonStepPaths ((horizon + 1 : ℕ) : ℝ≥0) rates embedding))).map
      (finiteHorizonPathRestriction (horizon : ℝ≥0) ((horizon + 1 : ℕ) : ℝ≥0)
        (by exact_mod_cast Nat.le_succ horizon) rates embedding) =
    (laws horizon : Measure (FiniteSupportPathSpace
      (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding))) at compatibleMeasures
  unfold integerHorizonPrefixLaws
  rw [Measure.map_map (measurable_frestrictLe₂ (X := fun index : ℕ =>
    FiniteSupportPathSpace (finiteHorizonStepPaths (index : ℝ≥0) rates embedding)) (Nat.le_succ horizon))
      (integerHorizonPrefix_measurable rates embedding (horizon + 1))]
  have mapIdentity :
      (frestrictLe₂ (π := fun index : ℕ =>
        FiniteSupportPathSpace (finiteHorizonStepPaths (index : ℝ≥0) rates embedding)) (Nat.le_succ horizon)) ∘
        integerHorizonPrefix rates embedding (horizon + 1) =
      integerHorizonPrefix rates embedding horizon ∘
        finiteHorizonPathRestriction (horizon : ℝ≥0) ((horizon + 1 : ℕ) : ℝ≥0)
          (by exact_mod_cast Nat.le_succ horizon) rates embedding := by
    funext path index
    exact (integerHorizonPrefix_comp_restriction rates embedding horizon (horizon + 1)
      (Nat.le_succ horizon) path index).symm
  rw [mapIdentity, ← Measure.map_map (integerHorizonPrefix_measurable rates embedding horizon)
    (finiteHorizonPathRestriction_continuous (horizon : ℝ≥0) ((horizon + 1 : ℕ) : ℝ≥0)
      (by exact_mod_cast Nat.le_succ horizon) rates embedding).measurable, compatibleMeasures]

include compatible in
theorem exists_integerHorizon_familyLaw :
    ∃ familyLaw : ProbabilityMeasure (IntegerHorizonPathFamily rates embedding),
      (∀ (horizon : ℕ), (familyLaw : Measure (IntegerHorizonPathFamily rates embedding)).map (frestrictLe horizon) =
        integerHorizonPrefixLaws rates embedding laws horizon) ∧
      (∀ (horizon : ℕ), (familyLaw : Measure (IntegerHorizonPathFamily rates embedding)).map (fun family => family horizon) = (laws horizon : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding)))) := by
  letI : ∀ (horizon : ℕ), Nonempty
      (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding)) :=
    fun horizon => nonempty_of_isProbabilityMeasure (laws horizon : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding)))
  let familyMeasure := DependentPrefix.coherentPathLaw (Space := fun horizon : ℕ => FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding)) (integerHorizonPrefixLaws rates embedding laws)
  have familyPrefixes (horizon : ℕ) : familyMeasure.map (frestrictLe horizon) =
      integerHorizonPrefixLaws rates embedding laws horizon :=
    DependentPrefix.coherentPathLaw_prefix (Space := fun horizon : ℕ => FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding)) (integerHorizonPrefixLaws rates embedding laws)
      (integerHorizonPrefixLaws_coherent rates embedding laws compatible) horizon
  refine ⟨⟨familyMeasure, inferInstance⟩, familyPrefixes, ?_⟩
  intro horizon
  have lastMeasurable : Measurable (fun history : (index : Finset.Iic horizon) →
      FiniteSupportPathSpace (finiteHorizonStepPaths (index.val : ℝ≥0) rates embedding) =>
        history ⟨horizon, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
  have prefixMeasurable : Measurable (frestrictLe horizon : IntegerHorizonPathFamily rates embedding →
      (index : Finset.Iic horizon) →
        FiniteSupportPathSpace (finiteHorizonStepPaths (index.val : ℝ≥0) rates embedding)) :=
    measurable_frestrictLe horizon
  calc
    familyMeasure.map (fun family => family horizon) =
        (familyMeasure.map (frestrictLe horizon)).map
          (fun history => history ⟨horizon, Finset.mem_Iic.mpr le_rfl⟩) := by
      rw [Measure.map_map lastMeasurable prefixMeasurable]
      rfl
    _ = (integerHorizonPrefixLaws rates embedding laws horizon).map
        (fun history => history ⟨horizon, Finset.mem_Iic.mpr le_rfl⟩) := by rw [familyPrefixes]
    _ = (laws horizon : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding))) := by
      unfold integerHorizonPrefixLaws
      rw [Measure.map_map lastMeasurable (integerHorizonPrefix_measurable rates embedding horizon)]
      have lastIdentity :
          (fun history => history ⟨horizon, Finset.mem_Iic.mpr le_rfl⟩) ∘
            integerHorizonPrefix rates embedding horizon = id := by
        funext path
        exact integerHorizonPrefix_last rates embedding horizon path
      rw [lastIdentity, Measure.map_id]

theorem integerHorizon_familyLaw_ae_good
    (familyLaw : ProbabilityMeasure (IntegerHorizonPathFamily rates embedding))
    (prefixIdentity : ∀ (horizon : ℕ), (familyLaw : Measure (IntegerHorizonPathFamily rates embedding)).map (frestrictLe horizon) =
      integerHorizonPrefixLaws rates embedding laws horizon)
    (coordinateIdentity : ∀ (horizon : ℕ), (familyLaw : Measure (IntegerHorizonPathFamily rates embedding)).map (fun family => family horizon) =
      (laws horizon : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding))))
    (continuousLaws : ∀ (horizon : ℕ), ∀ᵐ path ∂(laws horizon : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding))), Continuous (UniformFun.toFun path.val)) :
    ∀ᵐ family ∂(familyLaw : Measure (IntegerHorizonPathFamily rates embedding)), IntegerHorizonPathFamily.Good rates embedding family := by
  have continuousAE : ∀ᵐ family ∂(familyLaw : Measure (IntegerHorizonPathFamily rates embedding)),
      ∀ (horizon : ℕ), Continuous (UniformFun.toFun (family horizon).val) := by
    apply ae_all_iff.mpr
    intro horizon
    have projectedAE : ∀ᵐ path ∂(familyLaw : Measure (IntegerHorizonPathFamily rates embedding)).map
        (fun family => family horizon), Continuous (UniformFun.toFun path.val) := by
      rw [coordinateIdentity]
      exact continuousLaws horizon
    exact ae_of_ae_map (μ := (familyLaw : Measure (IntegerHorizonPathFamily rates embedding)))
      (p := fun path : FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding) =>
        Continuous (UniformFun.toFun path.val))
      (show Measurable (fun family : IntegerHorizonPathFamily rates embedding => family horizon)
        from measurable_pi_apply horizon).aemeasurable projectedAE
  have compatibleAE : ∀ᵐ family ∂(familyLaw : Measure (IntegerHorizonPathFamily rates embedding)),
      ∀ (shortHorizon longHorizon : ℕ) (ordered : shortHorizon ≤ longHorizon),
        finiteHorizonPathRestriction (shortHorizon : ℝ≥0) (longHorizon : ℝ≥0)
          (by exact_mod_cast ordered) rates embedding (family longHorizon) = family shortHorizon := by
    apply ae_all_iff.mpr
    intro shortHorizon
    apply ae_all_iff.mpr
    intro longHorizon
    apply ae_all_iff.mpr
    intro ordered
    let predicate (history : (index : Finset.Iic longHorizon) →
        FiniteSupportPathSpace (finiteHorizonStepPaths (index.val : ℝ≥0) rates embedding)) : Prop :=
      finiteHorizonPathRestriction (shortHorizon : ℝ≥0) (longHorizon : ℝ≥0)
        (by exact_mod_cast ordered) rates embedding
        (history ⟨longHorizon, Finset.mem_Iic.mpr le_rfl⟩) =
          history ⟨shortHorizon, Finset.mem_Iic.mpr ordered⟩
    have predicateMeasurable : MeasurableSet {history | predicate history} :=
      (isClosed_eq
        ((finiteHorizonPathRestriction_continuous (shortHorizon : ℝ≥0) (longHorizon : ℝ≥0)
          (by exact_mod_cast ordered) rates embedding).comp (continuous_apply (⟨longHorizon, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic longHorizon)))
        (continuous_apply (⟨shortHorizon, Finset.mem_Iic.mpr ordered⟩ : Finset.Iic longHorizon))).measurableSet
    have prefixAE : ∀ᵐ history ∂integerHorizonPrefixLaws rates embedding laws longHorizon, predicate history := by
      unfold integerHorizonPrefixLaws
      apply (ae_map_iff (integerHorizonPrefix_measurable rates embedding longHorizon).aemeasurable
        predicateMeasurable).mpr
      refine Eventually.of_forall fun path => ?_
      dsimp only [predicate]
      rw [integerHorizonPrefix_last]
      rfl
    have projectedAE : ∀ᵐ history ∂(familyLaw : Measure (IntegerHorizonPathFamily rates embedding)).map (frestrictLe longHorizon), predicate history := by
      rw [prefixIdentity]
      exact prefixAE
    exact ae_of_ae_map (measurable_frestrictLe longHorizon).aemeasurable projectedAE
  filter_upwards [continuousAE, compatibleAE] with family familyContinuous familyCompatible
  exact ⟨familyContinuous, familyCompatible⟩

include compatible in
theorem exists_continuousTimePathLaw_of_compatible_integer_horizons
    (continuousLaws : ∀ (horizon : ℕ), ∀ᵐ path ∂(laws horizon : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding))), Continuous (UniformFun.toFun path.val)) :
    ∃ pathLaw : ProbabilityMeasure (ContinuousTimePath State),
      ∀ (horizon dimension : ℕ) (times : Fin dimension → ℝ≥0)
        (timesInHorizon : ∀ index, (times index : ℝ) ≤ horizon),
        (pathLaw : Measure (ContinuousTimePath State)).map (fun path => fun index => path.val (times index)) =
          (laws horizon : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding))).map (fun path => fun index => UniformFun.toFun path.val
            ⟨(times index : ℝ), (times index).property, timesInHorizon index⟩) := by
  obtain ⟨familyLaw, prefixIdentity, coordinateIdentity⟩ :=
    exists_integerHorizon_familyLaw rates embedding laws compatible
  have goodAE := integerHorizon_familyLaw_ae_good rates embedding laws familyLaw
    prefixIdentity coordinateIdentity continuousLaws
  let fullLaw : ProbabilityMeasure (ContinuousTimePath State) :=
    familyLaw.map (integerHorizonReconstructedPath_measurable rates embedding).aemeasurable
  refine ⟨fullLaw, ?_⟩
  intro horizon dimension times timesInHorizon
  change ((familyLaw : Measure (IntegerHorizonPathFamily rates embedding)).map (integerHorizonReconstructedPath rates embedding)).map
    (fun path => fun index => path.val (times index)) = _
  have evaluationMeasurable : Measurable (fun path : ContinuousTimePath State =>
      fun index : Fin dimension => path.val (times index)) :=
    measurable_pi_lambda _ (fun index => (measurable_pi_apply (times index)).comp measurable_subtype_coe)
  rw [Measure.map_map evaluationMeasurable (integerHorizonReconstructedPath_measurable rates embedding)]
  calc
    (familyLaw : Measure (IntegerHorizonPathFamily rates embedding)).map
        ((fun path : ContinuousTimePath State => fun index => path.val (times index)) ∘
          integerHorizonReconstructedPath rates embedding) =
        (familyLaw : Measure (IntegerHorizonPathFamily rates embedding)).map (fun family => fun index => UniformFun.toFun (family horizon).val
          ⟨(times index : ℝ), (times index).property, timesInHorizon index⟩) := by
      apply Measure.map_congr
      filter_upwards [goodAE] with family good
      funext index
      exact integerHorizonReconstructedPath_eq_local rates embedding family good horizon
        (times index) (timesInHorizon index)
    _ = ((familyLaw : Measure (IntegerHorizonPathFamily rates embedding)).map (fun family => family horizon)).map
        (fun path => fun index => UniformFun.toFun path.val
          ⟨(times index : ℝ), (times index).property, timesInHorizon index⟩) := by
      rw [Measure.map_map
        (measurable_pi_lambda _ fun index => (finiteSupportPathSpace_continuous_eval
          (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding)
          ⟨(times index : ℝ), (times index).property, timesInHorizon index⟩).measurable)
        (measurable_pi_apply horizon)]
      rfl
    _ = _ := by rw [coordinateIdentity]

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.exists_integerHorizon_familyLaw
#print axioms IGS.Sec31.DiscreteMarkov.integerHorizon_familyLaw_ae_good
#print axioms IGS.Sec31.DiscreteMarkov.exists_continuousTimePathLaw_of_compatible_integer_horizons


