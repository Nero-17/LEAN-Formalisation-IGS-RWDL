import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-! The energy-plus-L2 Hilbert completion of a nonnegative quadratic form.
The completion map is constructed by extension. Its injectivity is deduced
from sequential closability, rather than supplied as a separate hypothesis.
The wrapper prevents the form norm from replacing the ambient subspace norm. -/

namespace IGS.Sec31

open Filter Topology UniformSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

structure QuadraticEnergySpace (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) where
  value : domain

namespace QuadraticEnergySpace

variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values)

def equivDomain : QuadraticEnergySpace domain form nonnegative ≃ domain where
  toFun := value
  invFun := fun values => ⟨values⟩
  left_inv := fun values => by cases values; rfl
  right_inv := fun _ => rfl

instance : AddCommGroup (QuadraticEnergySpace domain form nonnegative) :=
  (equivDomain domain form nonnegative).addCommGroup

instance : Module ℝ (QuadraticEnergySpace domain form nonnegative) :=
  (equivDomain domain form nonnegative).module ℝ

def linearEquivDomain : QuadraticEnergySpace domain form nonnegative ≃ₗ[ℝ] domain :=
  (equivDomain domain form nonnegative).linearEquiv ℝ

noncomputable def innerCore : InnerProductSpace.Core ℝ (QuadraticEnergySpace domain form nonnegative) where
  inner first second := form.associated first.value second.value +
    inner ℝ (first.value : H) (second.value : H)
  conj_inner_symm first second := by
    simp only [conj_trivial]
    rw [QuadraticMap.associated_isSymm ℝ form, real_inner_comm]
  re_inner_nonneg values := by
    simpa only [RCLike.re_to_real, QuadraticMap.associated_eq_self_apply,
      real_inner_self_eq_norm_sq] using add_nonneg (nonnegative values.value) (sq_nonneg ‖(values.value : H)‖)
  add_left first second third := by
    change form.associated (first.value + second.value) third.value +
      inner ℝ ((first.value : H) + second.value) third.value = _
    rw [map_add, LinearMap.add_apply, inner_add_left]
    ring
  smul_left first second scalar := by
    change form.associated (scalar • first.value) second.value +
      inner ℝ (scalar • (first.value : H)) second.value = _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, inner_smul_left, conj_trivial]
    ring
  definite values equality := by
    have normZero : ‖(values.value : H)‖ = 0 := by
      have energyNonnegative := nonnegative values.value
      simp only [QuadraticMap.associated_eq_self_apply, real_inner_self_eq_norm_sq] at equality
      nlinarith [norm_nonneg (values.value : H)]
    apply (equivDomain domain form nonnegative).injective
    apply Subtype.ext
    exact norm_eq_zero.mp normZero

noncomputable instance : NormedAddCommGroup (QuadraticEnergySpace domain form nonnegative) :=
  letI : InnerProductSpace.Core ℝ (QuadraticEnergySpace domain form nonnegative) := innerCore domain form nonnegative
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

noncomputable instance : InnerProductSpace ℝ (QuadraticEnergySpace domain form nonnegative) :=
  letI : InnerProductSpace.Core ℝ (QuadraticEnergySpace domain form nonnegative) := innerCore domain form nonnegative
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (QuadraticEnergySpace domain form nonnegative))

theorem norm_sq (values : QuadraticEnergySpace domain form nonnegative) :
    ‖values‖ ^ 2 = form values.value + ‖(values.value : H)‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℝ)]
  change form.associated values.value values.value + inner ℝ (values.value : H) values.value = _
  rw [QuadraticMap.associated_eq_self_apply, real_inner_self_eq_norm_sq]

theorem ambient_norm_le (values : QuadraticEnergySpace domain form nonnegative) :
    ‖(values.value : H)‖ ≤ ‖values‖ := by
  have identity := norm_sq domain form nonnegative values
  nlinarith [nonnegative values.value, norm_nonneg values, norm_nonneg (values.value : H)]

noncomputable def inclusion : QuadraticEnergySpace domain form nonnegative →L[ℝ] H :=
  (domain.subtype.comp (linearEquivDomain domain form nonnegative).toLinearMap).mkContinuous 1
    (fun values => by simpa only [one_mul] using ambient_norm_le domain form nonnegative values)

@[simp] theorem inclusion_apply (values : QuadraticEnergySpace domain form nonnegative) :
    inclusion domain form nonnegative values = (values.value : H) := rfl

noncomputable def completionMap : Completion (QuadraticEnergySpace domain form nonnegative) →L[ℝ] H :=
  (inclusion domain form nonnegative).extend Completion.toComplL

@[simp] theorem completionMap_coe (values : QuadraticEnergySpace domain form nonnegative) :
    completionMap domain form nonnegative (values : Completion (QuadraticEnergySpace domain form nonnegative)) =
      (values.value : H) := by
  exact ContinuousLinearMap.extend_eq _ Completion.denseRange_coe (Completion.isUniformInducing_coe _) values

theorem completionMap_norm_le (point : Completion (QuadraticEnergySpace domain form nonnegative)) :
    ‖completionMap domain form nonnegative point‖ ≤ ‖point‖ := by
  induction point using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih values => simpa only [completionMap_coe, Completion.norm_coe] using
      ambient_norm_le domain form nonnegative values

def SequentiallyClosable : Prop :=
  ∀ sequence : ℕ → domain,
    (∀ tolerance > 0, ∃ threshold, ∀ first ≥ threshold, ∀ second ≥ threshold,
      form (sequence first - sequence second) < tolerance) →
    Tendsto (fun index => (sequence index : H)) atTop (nhds 0) →
    Tendsto (fun index => form (sequence index)) atTop (nhds 0)

theorem completionMap_injective (closable : SequentiallyClosable domain form) :
    Function.Injective (completionMap domain form nonnegative) := by
  apply (injective_iff_map_eq_zero (completionMap domain form nonnegative)).mpr
  intro point pointZero
  obtain ⟨approximation, approximationInRange, approximationLimit⟩ :=
    mem_closure_iff_seq_limit.mp (Completion.denseRange_coe point)
  choose sequence sequenceEquality using approximationInRange
  have sequenceLimit : Tendsto
      (fun index => (sequence index : Completion (QuadraticEnergySpace domain form nonnegative)))
      atTop (nhds point) := by
    simpa only [sequenceEquality] using approximationLimit
  have ambientZero : Tendsto (fun index => ((sequence index).value : H)) atTop (nhds 0) := by
    have mapped := (completionMap domain form nonnegative).continuous.continuousAt.tendsto.comp sequenceLimit
    change Tendsto (fun index => completionMap domain form nonnegative
      (sequence index : Completion (QuadraticEnergySpace domain form nonnegative)))
      atTop (nhds (completionMap domain form nonnegative point)) at mapped
    simp only [completionMap_coe, pointZero] at mapped
    exact mapped
  have energyCauchy : ∀ tolerance > 0, ∃ threshold, ∀ first ≥ threshold, ∀ second ≥ threshold,
      form ((sequence first).value - (sequence second).value) < tolerance := by
    intro tolerance tolerancePositive
    obtain ⟨threshold, differenceSmall⟩ := Metric.cauchySeq_iff.mp sequenceLimit.cauchySeq
      (Real.sqrt tolerance) (Real.sqrt_pos.mpr tolerancePositive)
    refine ⟨threshold, fun first firstLarge second secondLarge => ?_⟩
    have small := differenceSmall first firstLarge second secondLarge
    rw [Completion.dist_eq] at small
    rw [dist_eq_norm] at small
    have normIdentity := norm_sq domain form nonnegative (sequence first - sequence second)
    change ‖sequence first - sequence second‖ ^ 2 =
      form ((sequence first).value - (sequence second).value) +
        ‖((sequence first).value : H) - (sequence second).value‖ ^ 2 at normIdentity
    nlinarith [Real.sq_sqrt tolerancePositive.le, norm_nonneg (sequence first - sequence second),
      Real.sqrt_nonneg tolerance, sq_nonneg ‖((sequence first).value : H) - (sequence second).value‖]
  have energyZero := closable (fun index => (sequence index).value) energyCauchy ambientZero
  have squaredNormZero : Tendsto (fun index => ‖sequence index‖ ^ 2) atTop (nhds 0) := by
    have sumZero := energyZero.add (ambientZero.norm.pow 2)
    simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero, ← norm_sq] using sumZero
  have normZero : Tendsto (fun index => ‖sequence index‖) atTop (nhds 0) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using squaredNormZero.sqrt
  have normLimit := sequenceLimit.norm
  simp only [Completion.norm_coe] at normLimit
  exact norm_eq_zero.mp (tendsto_nhds_unique normLimit normZero)

noncomputable def closedDomain : Submodule ℝ H := (completionMap domain form nonnegative).range

noncomputable def closedDomainEquiv (closable : SequentiallyClosable domain form) :
    Completion (QuadraticEnergySpace domain form nonnegative) ≃ₗ[ℝ] closedDomain domain form nonnegative :=
  LinearEquiv.ofInjective (completionMap domain form nonnegative).toLinearMap
    (completionMap_injective domain form nonnegative closable)

noncomputable def closedForm (closable : SequentiallyClosable domain form) :
    QuadraticForm ℝ (closedDomain domain form nonnegative) :=
  ((LinearMap.BilinMap.toQuadraticMap (innerₗ (Completion (QuadraticEnergySpace domain form nonnegative)))).comp
      (closedDomainEquiv domain form nonnegative closable).symm.toLinearMap) -
    ((LinearMap.BilinMap.toQuadraticMap (innerₗ H)).comp (closedDomain domain form nonnegative).subtype)

theorem closedForm_value (closable : SequentiallyClosable domain form)
    (values : closedDomain domain form nonnegative) :
    closedForm domain form nonnegative closable values =
      ‖(closedDomainEquiv domain form nonnegative closable).symm values‖ ^ 2 - ‖(values : H)‖ ^ 2 := by
  simp only [closedForm, QuadraticMap.sub_apply, QuadraticMap.comp_apply,
    LinearMap.BilinMap.toQuadraticMap_apply, innerₗ_apply_apply, real_inner_self_eq_norm_sq]
  rfl

theorem closedForm_nonnegative (closable : SequentiallyClosable domain form)
    (values : closedDomain domain form nonnegative) :
    0 ≤ closedForm domain form nonnegative closable values := by
  rw [closedForm_value]
  have bound := completionMap_norm_le domain form nonnegative
    ((closedDomainEquiv domain form nonnegative closable).symm values)
  have agreement : completionMap domain form nonnegative
      ((closedDomainEquiv domain form nonnegative closable).symm values) = (values : H) :=
    congrArg Subtype.val ((closedDomainEquiv domain form nonnegative closable).apply_symm_apply values)
  rw [agreement] at bound
  nlinarith [norm_nonneg (values : H), norm_nonneg ((closedDomainEquiv domain form nonnegative closable).symm values)]

theorem original_mem_closedDomain (values : domain) : (values : H) ∈ closedDomain domain form nonnegative :=
  ⟨((⟨values⟩ : QuadraticEnergySpace domain form nonnegative) : Completion (QuadraticEnergySpace domain form nonnegative)),
    completionMap_coe domain form nonnegative _⟩

theorem closedForm_extends (closable : SequentiallyClosable domain form) (values : domain) :
    closedForm domain form nonnegative closable
      ⟨(values : H), original_mem_closedDomain domain form nonnegative values⟩ = form values := by
  have inverseValue : (closedDomainEquiv domain form nonnegative closable).symm
      ⟨(values : H), original_mem_closedDomain domain form nonnegative values⟩ =
        ((⟨values⟩ : QuadraticEnergySpace domain form nonnegative) : Completion (QuadraticEnergySpace domain form nonnegative)) := by
    apply completionMap_injective domain form nonnegative closable
    rw [completionMap_coe]
    exact congrArg Subtype.val ((closedDomainEquiv domain form nonnegative closable).apply_symm_apply _)
  rw [closedForm_value, inverseValue, Completion.norm_coe, norm_sq]
  simp

/-- The completed domain carries its energy-plus-ambient norm, distinct from
the possibly incomplete ambient subspace norm. -/
noncomputable def closedSpaceEquiv (closable : SequentiallyClosable domain form) :
    QuadraticEnergySpace (closedDomain domain form nonnegative)
        (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable) ≃ₗᵢ[ℝ]
      Completion (QuadraticEnergySpace domain form nonnegative) :=
  { (linearEquivDomain (closedDomain domain form nonnegative)
        (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable)).trans
      (closedDomainEquiv domain form nonnegative closable).symm with
    norm_map' := by
      intro values
      have energyIdentity := norm_sq (closedDomain domain form nonnegative)
        (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable) values
      rw [closedForm_value] at energyIdentity
      change ‖(closedDomainEquiv domain form nonnegative closable).symm values.value‖ = ‖values‖
      nlinarith [norm_nonneg values,
        norm_nonneg ((closedDomainEquiv domain form nonnegative closable).symm values.value)] }

theorem closedEnergySpace_complete (closable : SequentiallyClosable domain form) :
    CompleteSpace (QuadraticEnergySpace (closedDomain domain form nonnegative)
      (closedForm domain form nonnegative closable) (closedForm_nonnegative domain form nonnegative closable)) :=
  (closedSpaceEquiv domain form nonnegative closable).toIsometryEquiv.completeSpace

theorem closedDomain_dense (domainDense : Dense (domain : Set H)) :
    Dense (closedDomain domain form nonnegative : Set H) := by
  apply domainDense.mono
  intro values membership
  exact original_mem_closedDomain domain form nonnegative ⟨values, membership⟩

end QuadraticEnergySpace

end IGS.Sec31

#print axioms IGS.Sec31.QuadraticEnergySpace.completionMap_coe
#print axioms IGS.Sec31.QuadraticEnergySpace.completionMap_injective
#print axioms IGS.Sec31.QuadraticEnergySpace.closedForm_nonnegative
#print axioms IGS.Sec31.QuadraticEnergySpace.closedForm_extends
#print axioms IGS.Sec31.QuadraticEnergySpace.closedEnergySpace_complete
#print axioms IGS.Sec31.QuadraticEnergySpace.closedDomain_dense
