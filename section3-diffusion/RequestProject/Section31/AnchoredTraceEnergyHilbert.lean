import RequestProject.Section31.TraceEnergyAnchoredCompleteness
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Algebra.Module.TransferInstance

/-! The constructed finite-trace energy, plus one anchored value, defines a
complete real inner product space. This provides the Hilbert step in the
resistance-form construction. It does not assert continuity of all functions
on a separate metric completion or assume that completeness step. -/

namespace IGS.Sec31

open Filter Topology
noncomputable section
variable {Vertex : Type*}

structure AnchoredTraceEnergySpace (networks : ℕ → FiniteNetwork Vertex)
    (energyIncreasing : ∀ values : Vertex → ℝ, Monotone (fun level => (networks level).energy values))
    (anchor : Vertex)
    (evaluation : ∀ vertex, ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ values : traceEnergyDomain networks, (values.val vertex) ^ 2 ≤
        coefficient * (traceEnergyValue networks values + (values.val anchor) ^ 2)) where
  value : traceEnergyDomain networks

namespace AnchoredTraceEnergySpace

variable (networks : ℕ → FiniteNetwork Vertex)
    (energyIncreasing : ∀ values : Vertex → ℝ, Monotone (fun level => (networks level).energy values))
    (anchor : Vertex)
    (evaluation : ∀ vertex, ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ values : traceEnergyDomain networks, (values.val vertex) ^ 2 ≤
        coefficient * (traceEnergyValue networks values + (values.val anchor) ^ 2))

def equivDomain : AnchoredTraceEnergySpace networks energyIncreasing anchor evaluation ≃
    traceEnergyDomain networks where
  toFun := value
  invFun := fun values => ⟨values⟩
  left_inv := fun values => by cases values; rfl
  right_inv := fun _ => rfl

instance : AddCommGroup (AnchoredTraceEnergySpace networks energyIncreasing anchor evaluation) :=
  (equivDomain networks energyIncreasing anchor evaluation).addCommGroup

instance : Module ℝ (AnchoredTraceEnergySpace networks energyIncreasing anchor evaluation) :=
  (equivDomain networks energyIncreasing anchor evaluation).module ℝ

def innerCore : InnerProductSpace.Core ℝ
    (AnchoredTraceEnergySpace networks energyIncreasing anchor evaluation) where
  inner first second := (limitTraceQuadraticForm networks energyIncreasing).associated first.value second.value +
    first.value.val anchor * second.value.val anchor
  conj_inner_symm first second := by
    simp only [conj_trivial]
    rw [QuadraticMap.associated_isSymm ℝ (limitTraceQuadraticForm networks energyIncreasing), mul_comm]
  re_inner_nonneg values := by
    simpa only [RCLike.re_to_real, QuadraticMap.associated_eq_self_apply, ← pow_two] using
      add_nonneg (limitTraceQuadraticForm_nonneg networks energyIncreasing values.value)
        (sq_nonneg (values.value.val anchor))
  add_left first second third := by
    change (limitTraceQuadraticForm networks energyIncreasing).associated
      (first.value + second.value) third.value +
      (first.value.val anchor + second.value.val anchor) * third.value.val anchor = _
    rw [map_add, LinearMap.add_apply]
    ring
  smul_left first second scalar := by
    change (limitTraceQuadraticForm networks energyIncreasing).associated
      (scalar • first.value) second.value +
      (scalar * first.value.val anchor) * second.value.val anchor = _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, conj_trivial]
    ring
  definite values equality := by
    simp only [QuadraticMap.associated_eq_self_apply, ← pow_two] at equality
    apply (equivDomain networks energyIncreasing anchor evaluation).injective
    apply Subtype.ext
    funext vertex
    change values.value.val vertex = 0
    obtain ⟨coefficient, _, control⟩ := evaluation vertex
    have bounded := control values.value
    change (values.value.val vertex) ^ 2 ≤ coefficient *
      (limitTraceQuadraticForm networks energyIncreasing values.value + (values.value.val anchor) ^ 2) at bounded
    rw [equality, mul_zero] at bounded
    nlinarith [sq_nonneg (values.value.val vertex)]

instance : NormedAddCommGroup (AnchoredTraceEnergySpace networks energyIncreasing anchor evaluation) :=
  letI : InnerProductSpace.Core ℝ (AnchoredTraceEnergySpace networks energyIncreasing anchor evaluation) :=
    innerCore networks energyIncreasing anchor evaluation
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance : InnerProductSpace ℝ (AnchoredTraceEnergySpace networks energyIncreasing anchor evaluation) :=
  letI : InnerProductSpace.Core ℝ (AnchoredTraceEnergySpace networks energyIncreasing anchor evaluation) :=
    innerCore networks energyIncreasing anchor evaluation
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ
    (AnchoredTraceEnergySpace networks energyIncreasing anchor evaluation))

theorem norm_sq (values : AnchoredTraceEnergySpace networks energyIncreasing anchor evaluation) :
    ‖values‖ ^ 2 = traceEnergyValue networks values.value + (values.value.val anchor) ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℝ)]
  change (limitTraceQuadraticForm networks energyIncreasing).associated values.value values.value +
    values.value.val anchor * values.value.val anchor = _
  rw [QuadraticMap.associated_eq_self_apply]
  change traceEnergyValue networks values.value + values.value.val anchor * values.value.val anchor = _
  ring

instance : CompleteSpace (AnchoredTraceEnergySpace networks energyIncreasing anchor evaluation) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro sequence sequenceCauchy
  have energyCauchy : ∀ tolerance > 0, ∃ threshold : ℕ,
      ∀ first ≥ threshold, ∀ second ≥ threshold,
        traceEnergyValue networks ((sequence first).value - (sequence second).value) +
          ((sequence first).value.val anchor - (sequence second).value.val anchor) ^ 2 < tolerance := by
    intro tolerance positive
    obtain ⟨threshold, small⟩ := Metric.cauchySeq_iff.mp sequenceCauchy
      (Real.sqrt tolerance / 2) (by positivity)
    refine ⟨threshold, fun first firstAfter second secondAfter => ?_⟩
    have close := small first firstAfter second secondAfter
    rw [dist_eq_norm] at close
    have identity := norm_sq networks energyIncreasing anchor evaluation (sequence first - sequence second)
    change ‖sequence first - sequence second‖ ^ 2 =
      traceEnergyValue networks ((sequence first).value - (sequence second).value) +
        ((sequence first).value.val anchor - (sequence second).value.val anchor) ^ 2 at identity
    rw [← identity]
    nlinarith [norm_nonneg (sequence first - sequence second), Real.sqrt_nonneg tolerance,
      Real.sq_sqrt positive.le]
  obtain ⟨limit, _, small⟩ := exists_traceEnergy_anchored_cauchy_limit networks anchor evaluation
    (fun index => (sequence index).value) energyCauchy
  refine ⟨⟨limit⟩, Metric.tendsto_atTop.mpr ?_⟩
  intro tolerance positive
  obtain ⟨threshold, eventuallySmall⟩ := eventually_atTop.mp (small (tolerance ^ 2 / 2) (by positivity))
  refine ⟨threshold, fun index after => ?_⟩
  have bounded := eventuallySmall index after
  have identity := norm_sq networks energyIncreasing anchor evaluation (sequence index - ⟨limit⟩)
  change ‖sequence index - ⟨limit⟩‖ ^ 2 = traceEnergyValue networks ((sequence index).value - limit) +
    ((sequence index).value.val anchor - limit.val anchor) ^ 2 at identity
  rw [← identity] at bounded
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (sequence index - (⟨limit⟩ :
    AnchoredTraceEnergySpace networks energyIncreasing anchor evaluation))]

end AnchoredTraceEnergySpace
end
end IGS.Sec31

#print axioms IGS.Sec31.AnchoredTraceEnergySpace.innerCore
#print axioms IGS.Sec31.AnchoredTraceEnergySpace.norm_sq
#print axioms IGS.Sec31.AnchoredTraceEnergySpace.instCompleteSpace
