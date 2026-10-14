import RequestProject.Section31.FiniteHorizonPathRestriction
import Mathlib.Algebra.Order.Floor.Ring

/-! A compatible sequence of continuous integer-horizon paths determines a
single continuous nonnegative-real-time path. The measurable target uses the
sigma algebra induced by evaluations; compact-open Borel identification is
not asserted here. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped UniformConvergence NNReal Classical
noncomputable section
set_option maxHeartbeats 4000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]
variable (rates : ℕ → ℝ≥0) (embedding : (level : ℕ) → Vertex level → State)

abbrev IntegerHorizonPathFamily :=
  (horizon : ℕ) → FiniteSupportPathSpace (finiteHorizonStepPaths (horizon : ℝ≥0) rates embedding)

def IntegerHorizonPathFamily.Good (family : IntegerHorizonPathFamily rates embedding) : Prop :=
  (∀ horizon, Continuous (UniformFun.toFun (family horizon).val)) ∧
    ∀ (shortHorizon longHorizon : ℕ) (ordered : shortHorizon ≤ longHorizon),
      finiteHorizonPathRestriction (shortHorizon : ℝ≥0) (longHorizon : ℝ≥0)
        (by exact_mod_cast ordered) rates embedding (family longHorizon) = family shortHorizon

theorem integerHorizonPathFamily_good_isClosed :
    IsClosed {family : IntegerHorizonPathFamily rates embedding | IntegerHorizonPathFamily.Good rates embedding family} := by
  letI : ∀ level, MeasurableSpace (Vertex level) := fun _ => ⊤
  have continuousClosed (horizon : ℕ) :
      IsClosed {family : IntegerHorizonPathFamily rates embedding |
        Continuous (UniformFun.toFun (family horizon).val)} :=
    (UniformFun.isClosed_setOf_continuous _).preimage
      (continuous_subtype_val.comp (continuous_apply horizon))
  have compatibleClosed (shortHorizon longHorizon : ℕ) (ordered : shortHorizon ≤ longHorizon) :
      IsClosed {family : IntegerHorizonPathFamily rates embedding |
        finiteHorizonPathRestriction (shortHorizon : ℝ≥0) (longHorizon : ℝ≥0)
          (by exact_mod_cast ordered) rates embedding (family longHorizon) = family shortHorizon} :=
    isClosed_eq
      ((finiteHorizonPathRestriction_continuous (shortHorizon : ℝ≥0) (longHorizon : ℝ≥0)
        (by exact_mod_cast ordered) rates embedding).comp (continuous_apply longHorizon))
      (continuous_apply shortHorizon)
  simpa only [IntegerHorizonPathFamily.Good, setOf_and, setOf_forall] using
    (isClosed_iInter continuousClosed).inter
      (isClosed_iInter fun shortHorizon => isClosed_iInter fun longHorizon =>
        isClosed_iInter fun ordered => compatibleClosed shortHorizon longHorizon ordered)

def integerHorizonAbove (time : ℝ≥0) : ℕ := ⌈(time : ℝ)⌉₊ + 1

theorem time_le_integerHorizonAbove (time : ℝ≥0) : (time : ℝ) ≤ (integerHorizonAbove time : ℝ) := by
  exact (Nat.le_ceil (time : ℝ)).trans (by simp only [integerHorizonAbove, Nat.cast_add, Nat.cast_one]; linarith)

def integerHorizonGlobalPath (family : IntegerHorizonPathFamily rates embedding) (time : ℝ≥0) : State :=
  UniformFun.toFun (family (integerHorizonAbove time)).val
    ⟨(time : ℝ), time.property, time_le_integerHorizonAbove time⟩

theorem integerHorizonGlobalPath_eq_local
    (family : IntegerHorizonPathFamily rates embedding) (good : IntegerHorizonPathFamily.Good rates embedding family)
    (horizon : ℕ) (time : ℝ≥0) (timeBound : (time : ℝ) ≤ horizon) :
    integerHorizonGlobalPath rates embedding family time =
      UniformFun.toFun (family horizon).val ⟨(time : ℝ), time.property, timeBound⟩ := by
  rcases le_total (integerHorizonAbove time) horizon with ordered | ordered
  · have equality := congrArg (fun path => UniformFun.toFun path.val
        ⟨(time : ℝ), time.property, time_le_integerHorizonAbove time⟩)
      (good.2 (integerHorizonAbove time) horizon ordered)
    exact equality.symm
  · have equality := congrArg (fun path => UniformFun.toFun path.val
        ⟨(time : ℝ), time.property, timeBound⟩)
      (good.2 horizon (integerHorizonAbove time) ordered)
    exact equality

theorem integerHorizonGlobalPath_continuous
    (family : IntegerHorizonPathFamily rates embedding) (good : IntegerHorizonPathFamily.Good rates embedding family) :
    Continuous (integerHorizonGlobalPath rates embedding family) := by
  apply continuous_iff_continuousAt.mpr
  intro time
  obtain ⟨horizon, timeBound⟩ := exists_nat_gt (time : ℝ)
  let localPath (location : ℝ≥0) : State := UniformFun.toFun (family horizon).val
    ⟨min (location : ℝ) (horizon : ℝ),
      le_min location.property (Nat.cast_nonneg horizon), min_le_right _ _⟩
  have localContinuous : Continuous localPath :=
    (good.1 horizon).comp
      ((NNReal.continuous_coe.min continuous_const).subtype_mk _)
  have near : ∀ᶠ location : ℝ≥0 in 𝓝 time, (location : ℝ) < horizon :=
    (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds timeBound
  apply localContinuous.continuousAt.congr
  filter_upwards [near] with location locationBound
  have localEquality := integerHorizonGlobalPath_eq_local rates embedding family good horizon location locationBound.le
  simpa only [localPath, min_eq_left locationBound.le] using localEquality.symm

theorem integerHorizonGlobalPath_measurable :
    Measurable (integerHorizonGlobalPath rates embedding) := by
  apply measurable_pi_lambda
  intro time
  exact (finiteSupportPathSpace_continuous_eval
    (finiteHorizonStepPaths (integerHorizonAbove time : ℝ≥0) rates embedding)
    ⟨(time : ℝ), time.property, time_le_integerHorizonAbove time⟩).measurable.comp
      (measurable_pi_apply (integerHorizonAbove time))

/-- Continuous paths with the sigma algebra induced by coordinate evaluation. -/
abbrev ContinuousTimePath (State : Type*) [TopologicalSpace State] :=
  {path : ℝ≥0 → State // Continuous path}

variable [Nonempty State]

def integerHorizonReconstructedRawPath (family : IntegerHorizonPathFamily rates embedding) : ℝ≥0 → State :=
  if IntegerHorizonPathFamily.Good rates embedding family then integerHorizonGlobalPath rates embedding family
  else fun _ => Classical.choice (inferInstance : Nonempty State)

theorem integerHorizonReconstructedRawPath_continuous (family : IntegerHorizonPathFamily rates embedding) :
    Continuous (integerHorizonReconstructedRawPath rates embedding family) := by
  by_cases good : IntegerHorizonPathFamily.Good rates embedding family
  · simpa only [integerHorizonReconstructedRawPath, if_pos good] using
      integerHorizonGlobalPath_continuous rates embedding family good
  · simpa only [integerHorizonReconstructedRawPath, if_neg good] using
      (continuous_const : Continuous (fun _ : ℝ≥0 => Classical.choice (inferInstance : Nonempty State)))

def integerHorizonReconstructedPath (family : IntegerHorizonPathFamily rates embedding) : ContinuousTimePath State :=
  ⟨integerHorizonReconstructedRawPath rates embedding family,
    integerHorizonReconstructedRawPath_continuous rates embedding family⟩

theorem integerHorizonReconstructedPath_measurable :
    Measurable (integerHorizonReconstructedPath rates embedding) := by
  apply Measurable.subtype_mk
  exact Measurable.ite (integerHorizonPathFamily_good_isClosed rates embedding).measurableSet
    (integerHorizonGlobalPath_measurable rates embedding) measurable_const

theorem integerHorizonReconstructedPath_eq_local
    (family : IntegerHorizonPathFamily rates embedding) (good : IntegerHorizonPathFamily.Good rates embedding family)
    (horizon : ℕ) (time : ℝ≥0) (timeBound : (time : ℝ) ≤ horizon) :
    (integerHorizonReconstructedPath rates embedding family).val time =
      UniformFun.toFun (family horizon).val ⟨(time : ℝ), time.property, timeBound⟩ := by
  change integerHorizonReconstructedRawPath rates embedding family time = _
  rw [integerHorizonReconstructedRawPath, if_pos good]
  exact integerHorizonGlobalPath_eq_local rates embedding family good horizon time timeBound

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.integerHorizonGlobalPath_continuous
#print axioms IGS.Sec31.DiscreteMarkov.integerHorizonReconstructedPath_measurable
#print axioms IGS.Sec31.DiscreteMarkov.integerHorizonReconstructedPath_eq_local
