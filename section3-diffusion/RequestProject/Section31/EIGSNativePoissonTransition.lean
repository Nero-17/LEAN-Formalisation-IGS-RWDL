import RequestProject.Section31.EIGSNativePoissonizedWalk
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Finite-vertex transition laws of the actual Poissonized native walk.
Discrete laws use powers of the actual `transProb` matrix; the jump count is
the actual mathlib Poisson PMF at the exact finite jump rate times time. The
finite transition PMF is identified with their genuine PMF bind. No path-law
or finite-dimensional-distribution convergence is asserted. -/

namespace EIGS

open MeasureTheory IGS.Sec31 Filter Topology
open scoped BigOperators NNReal ENNReal Classical

noncomputable section

set_option maxHeartbeats 4000000

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ)

/-- Every native finite vertex evaluation is a genuine continuous functional. -/
def xiNativeVertexEvaluation (vertex : XiVtx system level) :
    Lp ℝ 2 (xiVertexSpeedMeasure system mass level) →L[ℝ] ℝ := by
  letI : FiniteDimensional ℝ (Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :=
    (xiNativeEvaluationLinearEquiv system rulesConnected mass level).symm.finiteDimensional
  exact ((LinearMap.proj vertex).comp
    (xiNativeEvaluationLinearEquiv system rulesConnected mass level).toLinearMap).toContinuousLinearMap

@[simp] theorem xiNativeVertexEvaluation_apply (vertex : XiVtx system level)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    xiNativeVertexEvaluation system rulesConnected mass level vertex values = values vertex := rfl

/-- The actual discrete transition function, explicitly typed as a matrix
so that its powers use matrix multiplication. -/
def xiNativeDiscreteTransitionMatrix : Matrix (XiVtx system level) (XiVtx system level) ℝ :=
  transProb (XiSimpleGraph system level)

/-- The powers of the actual native L² transition operator evaluate to the
powers of the already-defined actual discrete transition matrix. -/
theorem xiNativeRandomWalk_powers_matrix_apply (jumps : ℕ)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) (vertex : XiVtx system level) :
    (xiNativeRandomWalk system rulesConnected mass level ^ jumps) values vertex =
      ∑ other, (xiNativeDiscreteTransitionMatrix system level ^ jumps) vertex other * values other := by
  classical
  have matrixIdentity : (fun vertex =>
      (xiNativeRandomWalk system rulesConnected mass level ^ jumps) values vertex) =
      (xiNativeDiscreteTransitionMatrix system level ^ jumps).mulVec (fun vertex => values vertex) := by
    induction jumps with
    | zero => simp only [pow_zero, ContinuousLinearMap.one_apply, Matrix.one_mulVec]
    | succ jumps induction =>
        calc
          _ = (xiNativeDiscreteTransitionMatrix system level).mulVec (fun vertex =>
              (xiNativeRandomWalk system rulesConnected mass level ^ jumps) values vertex) := by
            funext vertex
            simp only [pow_succ', ContinuousLinearMap.mul_apply, xiNativeRandomWalk_apply,
              xiNativeDiscreteTransitionMatrix, Matrix.mulVec, dotProduct]
          _ = _ := by rw [induction, Matrix.mulVec_mulVec, pow_succ']
  exact congrFun matrixIdentity vertex

theorem xiNativeRandomWalk_powers_single (jumps : ℕ)
    (source target : XiVtx system level) :
    (xiNativeRandomWalk system rulesConnected mass level ^ jumps)
      (xiFiniteSpeedL2 system mass level (Pi.single target 1)) source =
      (xiNativeDiscreteTransitionMatrix system level ^ jumps) source target := by
  classical
  rw [xiNativeRandomWalk_powers_matrix_apply]
  simp_rw [xiFiniteSpeedL2_apply system rulesConnected mass level]
  change ((xiNativeDiscreteTransitionMatrix system level ^ jumps).mulVec (Pi.single target 1)) source = _
  rw [Matrix.mulVec_single_one]
  rfl

include rulesConnected mass in
theorem xiNativeDiscreteTransition_nonnegative (jumps : ℕ)
    (source target : XiVtx system level) :
    0 ≤ (xiNativeDiscreteTransitionMatrix system level ^ jumps) source target := by
  classical
  rw [← xiNativeRandomWalk_powers_single system rulesConnected mass level jumps source target]
  apply xiNativeRandomWalk_powers_preserve_nonnegative system rulesConnected mass level
    (xiFiniteSpeedL2 system mass level (Pi.single target 1)) _ jumps source
  intro vertex
  rw [xiFiniteSpeedL2_apply system rulesConnected mass level]
  simp only [Pi.single_apply]
  split_ifs <;> norm_num

variable (resistanceRate normalization : ℝ)

/-- The actual finite transition coefficient, defined by the action on the
indicator of the terminal vertex. -/
def xiNativePoissonTransition (time : ℝ) (source target : XiVtx system level) : ℝ :=
  xiNativePoissonizedWalk system rulesConnected mass level resistanceRate normalization time
    (xiFiniteSpeedL2 system mass level (Pi.single target 1)) source

theorem xiNativePoissonTransition_hasSum (time : ℝ) (source target : XiVtx system level) :
    HasSum (fun jumps : ℕ => PoissonizedWalk.weight
      (time * xiNativeFiniteJumpRate system level resistanceRate normalization) jumps *
        (xiNativeDiscreteTransitionMatrix system level ^ jumps) source target)
      (xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization time source target) := by
  have valueSum := (xiNativeFiniteSemigroup_poisson_apply_hasSum system rulesConnected mass level
    resistanceRate normalization time (xiFiniteSpeedL2 system mass level (Pi.single target 1))).map
      (xiNativeVertexEvaluation system rulesConnected mass level source)
      (xiNativeVertexEvaluation system rulesConnected mass level source).continuous
  simpa only [Function.comp_def, map_smul, xiNativeVertexEvaluation_apply, smul_eq_mul,
    xiNativeRandomWalk_powers_single system rulesConnected mass level,
    xiNativePoissonTransition, xiNativePoissonizedWalk_eq_semigroup] using valueSum

theorem xiNativePoissonTransition_nonnegative
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (source target : XiVtx system level) :
    0 ≤ xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization time source target := by
  rw [← (xiNativePoissonTransition_hasSum system rulesConnected mass level resistanceRate normalization
    time source target).tsum_eq]
  exact tsum_nonneg fun jumps => mul_nonneg
    (xiNativePoissonizedWalk_weights_nonnegative system level resistanceRate normalization
      rateNonnegative normalizationNonnegative time timeNonnegative jumps)
    (xiNativeDiscreteTransition_nonnegative system rulesConnected mass level jumps source target)

include rulesConnected in
theorem xiNativeFiniteSpeedL2_single_decomposition
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    values = ∑ target : XiVtx system level,
      values target • xiFiniteSpeedL2 system mass level (Pi.single target 1) := by
  let equivalence := xiNativeEvaluationLinearEquiv system rulesConnected mass level
  have vectorDecomposition : equivalence values = ∑ target : XiVtx system level,
      values target • (Pi.single target (1 : ℝ) : XiVtx system level → ℝ) := by
    funext vertex
    change values vertex = (∑ target : XiVtx system level,
      values target • (Pi.single target (1 : ℝ) : XiVtx system level → ℝ)) vertex
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  have mapped := congrArg equivalence.symm vectorDecomposition
  simpa only [LinearEquiv.symm_apply_apply, map_sum, map_smul] using mapped

/-- The scalar transition coefficients reproduce the actual operator action
on every native finite L² vector. -/
theorem xiNativePoissonizedWalk_apply_transition (time : ℝ)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) (source : XiVtx system level) :
    xiNativePoissonizedWalk system rulesConnected mass level resistanceRate normalization time values source =
      ∑ target : XiVtx system level,
        xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization time source target *
          values target := by
  have mapped := congrArg (fun vector => xiNativeVertexEvaluation system rulesConnected mass level source
    (xiNativePoissonizedWalk system rulesConnected mass level resistanceRate normalization time vector))
      (xiNativeFiniteSpeedL2_single_decomposition system rulesConnected mass level values)
  simpa only [map_sum, map_smul, xiNativeVertexEvaluation_apply, smul_eq_mul,
    xiNativePoissonTransition, mul_comm] using mapped

variable (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))

include rulesConnected mass rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeDiscreteTransition_sum (jumps : ℕ) (source : XiVtx system level) :
    ∑ target : XiVtx system level,
      (xiNativeDiscreteTransitionMatrix system level ^ jumps) source target = 1 := by
  have constant := congrArg (fun values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level) => values source)
    (xiNativeRandomWalk_powers_preserve_one system rulesConnected mass level rulesLoopless rulesUnique
      plantingNonadjacent jumps)
  simpa only [xiNativeRandomWalk_powers_matrix_apply system rulesConnected mass level,
    xiFiniteSpeedL2_apply system rulesConnected mass level, mul_one] using constant

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativePoissonTransition_sum (time : ℝ) (source : XiVtx system level) :
    ∑ target : XiVtx system level,
      xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization time source target = 1 := by
  have action := xiNativePoissonizedWalk_apply_transition system rulesConnected mass level resistanceRate normalization
    time (xiFiniteSpeedL2 system mass level (fun _ => 1)) source
  have constant := congrArg (fun values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level) => values source)
    (xiNativePoissonizedWalk_preserves_one system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent time)
  simp only [xiFiniteSpeedL2_apply system rulesConnected mass level, mul_one] at action constant
  exact action.symm.trans constant

include rulesConnected mass rulesLoopless rulesUnique plantingNonadjacent in
def xiNativeDiscreteTransitionPMF (jumps : ℕ) (source : XiVtx system level) : PMF (XiVtx system level) :=
  PMF.ofFintype (fun target => ENNReal.ofReal
    ((xiNativeDiscreteTransitionMatrix system level ^ jumps) source target)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [xiNativeDiscreteTransition_sum system rulesConnected mass level rulesLoopless rulesUnique
          plantingNonadjacent jumps source, ENNReal.ofReal_one]
      · intro target _
        exact xiNativeDiscreteTransition_nonnegative system rulesConnected mass level jumps source target)

theorem xiNativeDiscreteTransitionPMF_apply (jumps : ℕ) (source target : XiVtx system level) :
    xiNativeDiscreteTransitionPMF system rulesConnected mass level rulesLoopless rulesUnique
      plantingNonadjacent jumps source target =
        ENNReal.ofReal ((xiNativeDiscreteTransitionMatrix system level ^ jumps) source target) := rfl

variable (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)

include system level resistanceRate normalization rateNonnegative normalizationNonnegative in
def xiNativeJumpCountPMF (time : ℝ≥0) : PMF ℕ :=
  ProbabilityTheory.poissonPMF ⟨(time : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization,
    mul_nonneg time.coe_nonneg (xiNativeFiniteJumpRate_nonnegative system level resistanceRate normalization
      rateNonnegative normalizationNonnegative)⟩

theorem xiNativeJumpCountPMF_apply (time : ℝ≥0) (jumps : ℕ) :
    xiNativeJumpCountPMF system level resistanceRate normalization rateNonnegative normalizationNonnegative time jumps =
      ENNReal.ofReal (PoissonizedWalk.weight
        ((time : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization) jumps) := by
  change ENNReal.ofReal (ProbabilityTheory.poissonPMFReal _ jumps) = _
  congr 1
  unfold ProbabilityTheory.poissonPMFReal PoissonizedWalk.weight
  dsimp only [NNReal.coe_mk]
  ring

include rulesConnected mass rulesLoopless rulesUnique plantingNonadjacent in
def xiNativePoissonTransitionPMF (time : ℝ≥0) (source : XiVtx system level) : PMF (XiVtx system level) :=
  PMF.ofFintype (fun target => ENNReal.ofReal
    (xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization time source target)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [xiNativePoissonTransition_sum system rulesConnected mass level resistanceRate normalization
          rulesLoopless rulesUnique plantingNonadjacent time source, ENNReal.ofReal_one]
      · intro target _
        exact xiNativePoissonTransition_nonnegative system rulesConnected mass level resistanceRate normalization
          rateNonnegative normalizationNonnegative time time.coe_nonneg source target)

theorem xiNativePoissonTransitionPMF_apply (time : ℝ≥0) (source target : XiVtx system level) :
    xiNativePoissonTransitionPMF system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source target =
        ENNReal.ofReal
          (xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization time source target) := rfl

/-- The actual finite transition law is obtained by first drawing the actual
Poisson jump count and then applying the actual discrete-walk transition law
for exactly that many jumps. -/
theorem xiNativePoissonTransitionPMF_eq_bind (time : ℝ≥0) (source : XiVtx system level) :
    xiNativePoissonTransitionPMF system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source =
    (xiNativeJumpCountPMF system level resistanceRate normalization rateNonnegative normalizationNonnegative time).bind
      (fun jumps => xiNativeDiscreteTransitionPMF system rulesConnected mass level rulesLoopless rulesUnique
        plantingNonadjacent jumps source) := by
  apply PMF.ext
  intro target
  rw [xiNativePoissonTransitionPMF_apply, PMF.bind_apply]
  simp only [xiNativeJumpCountPMF_apply, xiNativeDiscreteTransitionPMF_apply]
  have scalarSum := xiNativePoissonTransition_hasSum system rulesConnected mass level resistanceRate normalization
    time source target
  have termsNonnegative (jumps : ℕ) :
      0 ≤ PoissonizedWalk.weight
        ((time : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization) jumps *
          (xiNativeDiscreteTransitionMatrix system level ^ jumps) source target :=
    mul_nonneg (xiNativePoissonizedWalk_weights_nonnegative system level resistanceRate normalization
      rateNonnegative normalizationNonnegative time time.coe_nonneg jumps)
      (xiNativeDiscreteTransition_nonnegative system rulesConnected mass level jumps source target)
  calc
    _ = ENNReal.ofReal (∑' jumps : ℕ, PoissonizedWalk.weight
        ((time : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization) jumps *
          (xiNativeDiscreteTransitionMatrix system level ^ jumps) source target) :=
      congrArg ENNReal.ofReal scalarSum.tsum_eq.symm
    _ = ∑' jumps : ℕ, ENNReal.ofReal (PoissonizedWalk.weight
        ((time : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization) jumps *
          (xiNativeDiscreteTransitionMatrix system level ^ jumps) source target) :=
      ENNReal.ofReal_tsum_of_nonneg termsNonnegative scalarSum.summable
    _ = _ := by
      apply tsum_congr
      intro jumps
      exact ENNReal.ofReal_mul (xiNativePoissonizedWalk_weights_nonnegative system level resistanceRate normalization
        rateNonnegative normalizationNonnegative time time.coe_nonneg jumps)

@[simp] theorem xiNativePoissonTransition_zero (source target : XiVtx system level) :
    xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization 0 source target =
      if source = target then 1 else 0 := by
  rw [xiNativePoissonTransition, xiNativePoissonizedWalk_zero, ContinuousLinearMap.one_apply,
    xiFiniteSpeedL2_apply system rulesConnected mass level]
  simp [Pi.single_apply]

theorem xiNativePoissonTransition_of_zero_rate (time : ℝ)
    (rateZero : xiNativeFiniteJumpRate system level resistanceRate normalization = 0)
    (source target : XiVtx system level) :
    xiNativePoissonTransition system rulesConnected mass level resistanceRate normalization time source target =
      if source = target then 1 else 0 := by
  rw [xiNativePoissonTransition, xiNativePoissonizedWalk_of_zero_rate system rulesConnected mass level
    resistanceRate normalization time rateZero, ContinuousLinearMap.one_apply,
    xiFiniteSpeedL2_apply system rulesConnected mass level]
  simp [Pi.single_apply]

@[simp] theorem xiNativeJumpCountPMF_zero :
    xiNativeJumpCountPMF system level resistanceRate normalization rateNonnegative normalizationNonnegative 0 =
      PMF.pure 0 := by
  apply PMF.ext
  intro jumps
  rw [xiNativeJumpCountPMF_apply]
  simp only [NNReal.coe_zero, zero_mul, PoissonizedWalk.weight_zero_parameter, PMF.pure_apply]
  split_ifs <;> simp

@[simp] theorem xiNativePoissonTransitionPMF_zero (source : XiVtx system level) :
    xiNativePoissonTransitionPMF system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative 0 source =
        PMF.pure source := by
  apply PMF.ext
  intro target
  rw [xiNativePoissonTransitionPMF_apply]
  simp only [NNReal.coe_zero, xiNativePoissonTransition_zero, PMF.pure_apply]
  by_cases equality : source = target <;> simp [equality, eq_comm]

theorem xiNativePoissonTransitionPMF_of_zero_rate (time : ℝ≥0)
    (rateZero : xiNativeFiniteJumpRate system level resistanceRate normalization = 0)
    (source : XiVtx system level) :
    xiNativePoissonTransitionPMF system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source =
        PMF.pure source := by
  apply PMF.ext
  intro target
  rw [xiNativePoissonTransitionPMF_apply, xiNativePoissonTransition_of_zero_rate system rulesConnected mass level
    resistanceRate normalization time rateZero source target, PMF.pure_apply]
  by_cases equality : source = target <;> simp [equality, eq_comm]

/-- The transition PMF's singleton measure is the actual finite semigroup
evaluated on the actual terminal-vertex indicator. -/
theorem xiNativePoissonTransitionPMF_toMeasure_singleton (time : ℝ≥0)
    (source target : XiVtx system level) :
    (xiNativePoissonTransitionPMF system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source).toMeasure
        {target} = ENNReal.ofReal
      (xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time
        (xiFiniteSpeedL2 system mass level (Pi.single target 1)) source) := by
  rw [PMF.toMeasure_apply_singleton _ target (measurableSet_singleton target),
    xiNativePoissonTransitionPMF_apply, xiNativePoissonTransition, xiNativePoissonizedWalk_eq_semigroup]

/-- The genuine finite transition probability measure reproduces the actual
finite semigroup's source-point evaluation for every native vector. -/
theorem xiNativePoissonTransitionPMF_integral (time : ℝ≥0)
    (source : XiVtx system level) (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    ∫ target : XiVtx system level, values target ∂
      (xiNativePoissonTransitionPMF system rulesConnected mass level resistanceRate normalization
        rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative time source).toMeasure =
      xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time values source := by
  rw [integral_fintype _ Integrable.of_finite]
  simp_rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    xiNativePoissonTransitionPMF_apply, ENNReal.toReal_ofReal
      (xiNativePoissonTransition_nonnegative system rulesConnected mass level resistanceRate normalization
        rateNonnegative normalizationNonnegative time time.coe_nonneg source _), smul_eq_mul]
  rw [← xiNativePoissonizedWalk_apply_transition system rulesConnected mass level resistanceRate normalization,
    xiNativePoissonizedWalk_eq_semigroup]

end
end EIGS

#print axioms EIGS.xiNativeVertexEvaluation_apply
#print axioms EIGS.xiNativeRandomWalk_powers_matrix_apply
#print axioms EIGS.xiNativeRandomWalk_powers_single
#print axioms EIGS.xiNativeDiscreteTransition_nonnegative
#print axioms EIGS.xiNativePoissonTransition_hasSum
#print axioms EIGS.xiNativePoissonTransition_nonnegative
#print axioms EIGS.xiNativeFiniteSpeedL2_single_decomposition
#print axioms EIGS.xiNativePoissonizedWalk_apply_transition
#print axioms EIGS.xiNativeDiscreteTransition_sum
#print axioms EIGS.xiNativePoissonTransition_sum
#print axioms EIGS.xiNativeDiscreteTransitionPMF_apply
#print axioms EIGS.xiNativeJumpCountPMF_apply
#print axioms EIGS.xiNativePoissonTransitionPMF_apply
#print axioms EIGS.xiNativePoissonTransitionPMF_eq_bind
#print axioms EIGS.xiNativePoissonTransition_zero
#print axioms EIGS.xiNativePoissonTransition_of_zero_rate
#print axioms EIGS.xiNativeJumpCountPMF_zero
#print axioms EIGS.xiNativePoissonTransitionPMF_zero
#print axioms EIGS.xiNativePoissonTransitionPMF_of_zero_rate
#print axioms EIGS.xiNativePoissonTransitionPMF_toMeasure_singleton
#print axioms EIGS.xiNativePoissonTransitionPMF_integral
