import RequestProject.Section31.EIGSNativePoissonTransition
import RequestProject.Section31.QuadraticEnergySemigroupIntegralPreservation
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Invariance

/-! Actual finite probability kernels of the native Poissonized walk. Finite
vertex measurability bundles the already-constructed genuine PMF measures.
The zero and Chapman--Kolmogorov laws follow from the actual finite
semigroup, with no independent transition-identity premise. -/

namespace EIGS

open MeasureTheory ProbabilityTheory IGS.Sec31 Filter Topology
open scoped BigOperators NNReal ENNReal Classical ProbabilityTheory

noncomputable section

set_option maxHeartbeats 4000000

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ) (resistanceRate normalization : ℝ)

noncomputable local instance : NormedAlgebra ℚ
    (Lp ℝ 2 (xiVertexSpeedMeasure system mass level) →L[ℝ]
      Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

/-- The actual scalar transition coefficients satisfy composition because
the actual finite operator exponential satisfies addition of times. -/
theorem xiNativePoissonTransition_add (firstTime secondTime : ℝ)
    (source target : XiVtx system level) :
    xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization
      (firstTime + secondTime) source target =
    ∑ middle : XiVtx system level,
      xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization firstTime source middle *
        xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization secondTime middle target := by
  let indicator := xiFiniteSpeedL2 system mass level (Pi.single target 1)
  calc
    _ = xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization firstTime
        (xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization secondTime indicator) source := by
      rw [xiNativePoissonTransition, xiNativePoissonizedWalk_eq_semigroup,
        xiNativeFiniteSemigroup_add, ContinuousLinearMap.mul_apply]
    _ = ∑ middle : XiVtx system level,
        xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization firstTime source middle *
          xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization secondTime indicator middle := by
      simpa only [xiNativePoissonizedWalk_eq_semigroup] using
        xiNativePoissonizedWalk_apply_transition system rulesConnected mass level resistanceRate normalization
          firstTime (xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization
            secondTime indicator) source
    _ = _ := by simp only [xiNativePoissonTransition, xiNativePoissonizedWalk_eq_semigroup, indicator]

variable (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)

theorem xiNativeFiniteTransitionMeasure_measurable (time : ℝ≥0) :
    Measurable (fun source : XiVtx system level =>
      (xiNativePoissonTransitionPMF system rulesConnected mass level resistanceRate normalization
        rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source).toMeasure) :=
  measurable_of_countable _

/-- The genuine finite probability kernel, using the actual PMF measure at
each starting vertex. -/
def xiNativeFiniteKernel (time : ℝ≥0) : Kernel (XiVtx system level) (XiVtx system level) :=
  ⟨fun source => (xiNativePoissonTransitionPMF system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source).toMeasure,
    xiNativeFiniteTransitionMeasure_measurable system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time⟩

@[simp] theorem xiNativeFiniteKernel_apply (time : ℝ≥0) (source : XiVtx system level) :
    xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source =
    (xiNativePoissonTransitionPMF system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source).toMeasure := rfl

instance xiNativeFiniteKernel_isMarkov (time : ℝ≥0) :
    IsMarkovKernel (xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time) := by
  constructor
  intro source
  change IsProbabilityMeasure
    (xiNativePoissonTransitionPMF system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source).toMeasure
  infer_instance

theorem xiNativeFiniteKernel_apply_singleton (time : ℝ≥0) (source target : XiVtx system level) :
    xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source {target} =
    ENNReal.ofReal (xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization time source target) := by
  rw [xiNativeFiniteKernel_apply, PMF.toMeasure_apply_singleton _ target (measurableSet_singleton target),
    xiNativePoissonTransitionPMF_apply]

theorem xiNativeFiniteKernel_integral (time : ℝ≥0) (source : XiVtx system level)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    (∫ target : XiVtx system level, values target ∂
      xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
        rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source) =
    xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time values source :=
  xiNativePoissonTransitionPMF_integral system rulesConnected mass level resistanceRate normalization
    rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source values

@[simp] theorem xiNativeFiniteKernel_zero :
    xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative 0 = Kernel.id := by
  apply DFunLike.ext
  intro source
  rw [xiNativeFiniteKernel_apply, xiNativePoissonTransitionPMF_zero, PMF.toMeasure_pure, Kernel.id_apply]

theorem xiNativeFiniteKernel_add (firstTime secondTime : ℝ≥0) :
    xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative (firstTime + secondTime) =
    xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative secondTime ∘ₖ
    xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative firstTime := by
  apply DFunLike.ext
  intro source
  apply Measure.ext_of_singleton
  intro target
  rw [Kernel.comp_apply' _ _ source (measurableSet_singleton target), lintegral_fintype]
  simp_rw [xiNativeFiniteKernel_apply_singleton]
  rw [NNReal.coe_add, xiNativePoissonTransition_add]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro middle _
    rw [ENNReal.ofReal_mul (xiNativePoissonTransition_nonnegative system rulesConnected mass level
      resistanceRate normalization rateNonnegative normalizationNonnegative firstTime firstTime.coe_nonneg source middle),
      mul_comm]
  · intro middle _
    exact mul_nonneg
      (xiNativePoissonTransition_nonnegative system rulesConnected mass level resistanceRate normalization
        rateNonnegative normalizationNonnegative firstTime firstTime.coe_nonneg source middle)
      (xiNativePoissonTransition_nonnegative system rulesConnected mass level resistanceRate normalization
        rateNonnegative normalizationNonnegative secondTime secondTime.coe_nonneg middle target)

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeFiniteSemigroup_selfAdjoint (time : ℝ) :
    IsSelfAdjoint (xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time) := by
  exact ((IsSelfAdjoint.all (-time)).smul
    (xiNativeFiniteGenerator_selfAdjoint system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization)).exp

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeFiniteSemigroup_integral_preservation (time : ℝ)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    (∫ vertex : XiVtx system level,
      xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time values vertex
        ∂xiVertexSpeedMeasure system mass level) =
    ∫ vertex : XiVtx system level, values vertex ∂xiVertexSpeedMeasure system mass level := by
  let one := xiFiniteSpeedL2 system mass level (fun _ => 1)
  have oneAE : ∀ᵐ vertex ∂xiVertexSpeedMeasure system mass level, one vertex = 1 :=
    Eventually.of_forall fun vertex => xiFiniteSpeedL2_apply system rulesConnected mass level (fun _ => 1) vertex
  have onePreserved : xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time one = one := by
    simpa only [xiNativePoissonizedWalk_eq_semigroup] using
      xiNativePoissonizedWalk_preserves_one system rulesConnected mass level resistanceRate normalization
        rulesLoopless rulesUnique plantingNonadjacent time
  have pairing : inner ℝ
      (xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time values) one =
      inner ℝ values
        (xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time one) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (xiNativeFiniteSemigroup_selfAdjoint system rulesConnected mass level resistanceRate normalization
        rulesLoopless rulesUnique plantingNonadjacent time)) values one
  rw [onePreserved] at pairing
  simpa only [QuadraticEnergySpace.lp_inner_one_eq_integral
    (xiVertexSpeedMeasure system mass level) one oneAE] using pairing

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativePoissonTransition_stationary (time : ℝ≥0) (target : XiVtx system level) :
    ∑ source : XiVtx system level, (xiVertexSpeedMeasure system mass level).real {source} *
      xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization time source target =
    (xiVertexSpeedMeasure system mass level).real {target} := by
  have preservation := xiNativeFiniteSemigroup_integral_preservation system rulesConnected mass level
    resistanceRate normalization rulesLoopless rulesUnique plantingNonadjacent time
      (xiFiniteSpeedL2 system mass level (Pi.single target 1))
  rw [integral_fintype _ Integrable.of_finite, integral_fintype _ Integrable.of_finite] at preservation
  simpa [xiNativePoissonTransition, xiNativePoissonizedWalk_eq_semigroup,
    xiFiniteSpeedL2_apply system rulesConnected mass level, Pi.single_apply, smul_eq_mul] using preservation

/-- The actual native speed measure is invariant under the actual finite
kernel; invariance is derived from actual self-adjointness and preservation
of the actual constant-one vector. -/
theorem xiNativeFiniteKernel_invariant (time : ℝ≥0) :
    (xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time).Invariant
        (xiVertexSpeedMeasure system mass level) := by
  change (xiVertexSpeedMeasure system mass level).bind
    (xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time) =
        xiVertexSpeedMeasure system mass level
  apply Measure.ext_of_singleton
  intro target
  rw [Measure.bind_apply (measurableSet_singleton target) (Kernel.aemeasurable _), lintegral_fintype]
  simp_rw [xiNativeFiniteKernel_apply_singleton]
  have massAsReal (vertex : XiVtx system level) :
      xiVertexSpeedMeasure system mass level {vertex} =
        ENNReal.ofReal ((xiVertexSpeedMeasure system mass level).real {vertex}) := by
    exact (ENNReal.ofReal_toReal (measure_ne_top (xiVertexSpeedMeasure system mass level) {vertex})).symm
  simp_rw [massAsReal]
  calc
    _ = ∑ source : XiVtx system level, ENNReal.ofReal
        ((xiVertexSpeedMeasure system mass level).real {source} *
          xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization time source target) := by
      apply Finset.sum_congr rfl
      intro source _
      rw [ENNReal.ofReal_mul measureReal_nonneg, mul_comm]
    _ = ENNReal.ofReal (∑ source : XiVtx system level,
        (xiVertexSpeedMeasure system mass level).real {source} *
          xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization time source target) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro source _
      exact mul_nonneg measureReal_nonneg
        (xiNativePoissonTransition_nonnegative system rulesConnected mass level resistanceRate normalization
          rateNonnegative normalizationNonnegative time time.coe_nonneg source target)
    _ = _ := congrArg ENNReal.ofReal (xiNativePoissonTransition_stationary system rulesConnected mass level
      resistanceRate normalization rulesLoopless rulesUnique plantingNonadjacent time target)

end
end EIGS

#print axioms EIGS.xiNativePoissonTransition_add
#print axioms EIGS.xiNativeFiniteTransitionMeasure_measurable
#print axioms EIGS.xiNativeFiniteKernel_apply
#print axioms EIGS.xiNativeFiniteKernel_isMarkov
#print axioms EIGS.xiNativeFiniteKernel_apply_singleton
#print axioms EIGS.xiNativeFiniteKernel_integral
#print axioms EIGS.xiNativeFiniteKernel_zero
#print axioms EIGS.xiNativeFiniteKernel_add
#print axioms EIGS.xiNativeFiniteSemigroup_selfAdjoint
#print axioms EIGS.xiNativeFiniteSemigroup_integral_preservation
#print axioms EIGS.xiNativePoissonTransition_stationary
#print axioms EIGS.xiNativeFiniteKernel_invariant
