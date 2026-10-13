import RequestProject.Section31.EIGSNativeSemigroupConvergence
import RequestProject.Section31.BoundedYosidaInvariantConvex

/-! The actual finite random-walk exponential is the Poisson mixture of
powers of the actual discrete transition operator, at jump rate
`2 * normalization * resistanceRate ^ level * totalEdges`. The scalar
weights, their mass one, and the operator series are proved from the actual
exponential power series. This is an operator identification, not a path-law
convergence assertion. -/

namespace IGS.Sec31.PoissonizedWalk

open Filter Topology

noncomputable section

def weight (parameter : ℝ) (jumps : ℕ) : ℝ :=
  Real.exp (-parameter) * ((jumps.factorial : ℝ)⁻¹ * parameter ^ jumps)

theorem weight_nonnegative (parameter : ℝ) (parameterNonnegative : 0 ≤ parameter) (jumps : ℕ) :
    0 ≤ weight parameter jumps := by
  unfold weight
  positivity

theorem weights_hasSum (parameter : ℝ) : HasSum (weight parameter) 1 :=
  BoundedYosida.poisson_weights_hasSum parameter

@[simp] theorem weight_zero_parameter (jumps : ℕ) :
    weight 0 jumps = if jumps = 0 then 1 else 0 := by
  cases jumps <;> simp [weight]

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

noncomputable local instance : NormedAlgebra ℚ (Space →L[ℝ] Space) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

theorem exponential_identity (transition : Space →L[ℝ] Space) (rate time : ℝ) :
    NormedSpace.exp ((-time) • (rate • (1 - transition))) =
      Real.exp (-(time * rate)) • NormedSpace.exp ((time * rate) • transition) := by
  have exponentIdentity : (-time) • (rate • (1 - transition)) =
      (-(time * rate)) • (1 : Space →L[ℝ] Space) + (time * rate) • transition := by
    simp only [smul_sub, smul_smul, neg_mul, neg_smul]
    module
  have commuting : Commute ((-(time * rate)) • (1 : Space →L[ℝ] Space))
      ((time * rate) • transition) :=
    ((Commute.one_left transition).smul_left _).smul_right _
  rw [exponentIdentity, NormedSpace.exp_add_of_commute commuting,
    BoundedYosida.exp_smul_identity, smul_mul_assoc, one_mul]

theorem operator_hasSum (transition : Space →L[ℝ] Space) (rate time : ℝ) :
    HasSum (fun jumps : ℕ => weight (time * rate) jumps • transition ^ jumps)
      (NormedSpace.exp ((-time) • (rate • (1 - transition)))) := by
  have operatorSum := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
    ((time * rate) • transition)).const_smul (Real.exp (-(time * rate)))
  rw [exponential_identity]
  simpa only [weight, smul_pow, smul_smul, mul_assoc] using operatorSum

theorem apply_hasSum (transition : Space →L[ℝ] Space) (rate time : ℝ) (values : Space) :
    HasSum (fun jumps : ℕ => weight (time * rate) jumps • (transition ^ jumps) values)
      (NormedSpace.exp ((-time) • (rate • (1 - transition))) values) := by
  have valueSum := (operator_hasSum transition rate time).map
    (ContinuousLinearMap.apply ℝ Space values) (ContinuousLinearMap.apply ℝ Space values).continuous
  simpa only [Function.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.smul_apply] using valueSum

end
end IGS.Sec31.PoissonizedWalk

namespace EIGS

open MeasureTheory IGS.Sec31 Filter Topology
open scoped BigOperators NNReal

noncomputable section

set_option maxHeartbeats 4000000

variable {K : ℕ}

/-- The exact jump rate in the actual finite generator. -/
def xiNativeFiniteJumpRate (system : EIGSData K) (level : ℕ) (resistanceRate normalization : ℝ) : ℝ :=
  2 * normalization * resistanceRate ^ level * (totalEdges system.toRuleData level : ℝ)

theorem xiNativeFiniteJumpRate_nonnegative (system : EIGSData K) (level : ℕ)
    (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization) :
    0 ≤ xiNativeFiniteJumpRate system level resistanceRate normalization := by
  unfold xiNativeFiniteJumpRate
  positivity

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ) (resistanceRate normalization : ℝ)

noncomputable local instance : NormedAlgebra ℚ
    (Lp ℝ 2 (xiVertexSpeedMeasure system mass level) →L[ℝ]
      Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

theorem xiNativeFiniteGenerator_eq_jumpRate :
    xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization =
      xiNativeFiniteJumpRate system level resistanceRate normalization •
        (1 - xiNativeRandomWalk system rulesConnected mass level) := rfl

/-- A concrete Poisson mixture of powers of the actual native discrete walk. -/
def xiNativePoissonizedWalk (time : ℝ) :
    Lp ℝ 2 (xiVertexSpeedMeasure system mass level) →L[ℝ]
      Lp ℝ 2 (xiVertexSpeedMeasure system mass level) :=
  ∑' jumps : ℕ, PoissonizedWalk.weight
    (time * xiNativeFiniteJumpRate system level resistanceRate normalization) jumps •
      xiNativeRandomWalk system rulesConnected mass level ^ jumps

theorem xiNativeFiniteSemigroup_poisson_hasSum (time : ℝ) :
    HasSum (fun jumps : ℕ => PoissonizedWalk.weight
      (time * xiNativeFiniteJumpRate system level resistanceRate normalization) jumps •
        xiNativeRandomWalk system rulesConnected mass level ^ jumps)
      (xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time) :=
  PoissonizedWalk.operator_hasSum (xiNativeRandomWalk system rulesConnected mass level)
    (xiNativeFiniteJumpRate system level resistanceRate normalization) time

theorem xiNativePoissonizedWalk_eq_semigroup (time : ℝ) :
    xiNativePoissonizedWalk system rulesConnected mass level resistanceRate normalization time =
      xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time :=
  (xiNativeFiniteSemigroup_poisson_hasSum system rulesConnected mass level resistanceRate normalization time).tsum_eq

theorem xiNativeFiniteSemigroup_poisson_apply_hasSum (time : ℝ)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    HasSum (fun jumps : ℕ => PoissonizedWalk.weight
      (time * xiNativeFiniteJumpRate system level resistanceRate normalization) jumps •
        (xiNativeRandomWalk system rulesConnected mass level ^ jumps) values)
      (xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time values) :=
  PoissonizedWalk.apply_hasSum (xiNativeRandomWalk system rulesConnected mass level)
    (xiNativeFiniteJumpRate system level resistanceRate normalization) time values

theorem xiNativePoissonizedWalk_weights_nonnegative
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (jumps : ℕ) :
    0 ≤ PoissonizedWalk.weight
      (time * xiNativeFiniteJumpRate system level resistanceRate normalization) jumps :=
  PoissonizedWalk.weight_nonnegative _
    (mul_nonneg timeNonnegative (xiNativeFiniteJumpRate_nonnegative system level resistanceRate normalization
      rateNonnegative normalizationNonnegative)) jumps

@[simp] theorem xiNativePoissonizedWalk_zero :
    xiNativePoissonizedWalk system rulesConnected mass level resistanceRate normalization 0 = 1 := by
  rw [xiNativePoissonizedWalk_eq_semigroup, xiNativeFiniteSemigroup_zero]

theorem xiNativePoissonizedWalk_of_zero_rate (time : ℝ)
    (rateZero : xiNativeFiniteJumpRate system level resistanceRate normalization = 0) :
    xiNativePoissonizedWalk system rulesConnected mass level resistanceRate normalization time = 1 := by
  rw [xiNativePoissonizedWalk_eq_semigroup, xiNativeFiniteSemigroup,
    xiNativeFiniteGenerator_eq_jumpRate, rateZero, zero_smul, smul_zero, NormedSpace.exp_zero]

theorem xiNativeRandomWalk_preserves_nonnegative
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (nonnegative : ∀ vertex : XiVtx system level, 0 ≤ values vertex) :
    ∀ vertex : XiVtx system level,
      0 ≤ xiNativeRandomWalk system rulesConnected mass level values vertex := by
  classical
  intro vertex
  rw [xiNativeRandomWalk_apply]
  exact Finset.sum_nonneg fun other _ =>
    mul_nonneg (transProb_nonneg (G := XiSimpleGraph system level) vertex other) (nonnegative other)

theorem xiNativeRandomWalk_powers_preserve_nonnegative
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (nonnegative : ∀ vertex : XiVtx system level, 0 ≤ values vertex) (jumps : ℕ) :
    ∀ vertex : XiVtx system level,
      0 ≤ (xiNativeRandomWalk system rulesConnected mass level ^ jumps) values vertex := by
  induction jumps with
  | zero => simpa only [pow_zero, ContinuousLinearMap.one_apply] using nonnegative
  | succ jumps induction =>
      simpa only [pow_succ', ContinuousLinearMap.mul_apply] using
        xiNativeRandomWalk_preserves_nonnegative system rulesConnected mass level _ induction

variable (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeRandomWalk_preserves_one :
    xiNativeRandomWalk system rulesConnected mass level
      (xiFiniteSpeedL2 system mass level (fun _ => 1)) =
        xiFiniteSpeedL2 system mass level (fun _ => 1) := by
  classical
  apply (xiNativeEvaluationLinearEquiv system rulesConnected mass level).injective
  apply funext
  intro vertex
  change xiNativeRandomWalk system rulesConnected mass level
    (xiFiniteSpeedL2 system mass level (fun _ => 1)) vertex =
      xiFiniteSpeedL2 system mass level (fun _ => 1) vertex
  rw [xiNativeRandomWalk_apply]
  simp_rw [xiFiniteSpeedL2_apply system rulesConnected mass level]
  simp only [mul_one]
  apply transProb_sum
  rw [← xiVertexIncidenceCount_eq_degree system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent level vertex]
  exact xiVertexIncidenceCount_positive system rulesConnected level vertex

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeRandomWalk_powers_preserve_one (jumps : ℕ) :
    (xiNativeRandomWalk system rulesConnected mass level ^ jumps)
      (xiFiniteSpeedL2 system mass level (fun _ => 1)) =
        xiFiniteSpeedL2 system mass level (fun _ => 1) := by
  induction jumps with
  | zero => simp only [pow_zero, ContinuousLinearMap.one_apply]
  | succ jumps induction =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, induction]
      exact xiNativeRandomWalk_preserves_one system rulesConnected mass level rulesLoopless rulesUnique plantingNonadjacent

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativePoissonizedWalk_preserves_one (time : ℝ) :
    xiNativePoissonizedWalk system rulesConnected mass level resistanceRate normalization time
      (xiFiniteSpeedL2 system mass level (fun _ => 1)) =
        xiFiniteSpeedL2 system mass level (fun _ => 1) := by
  have walkSum := xiNativeFiniteSemigroup_poisson_apply_hasSum system rulesConnected mass level
    resistanceRate normalization time (xiFiniteSpeedL2 system mass level (fun _ => 1))
  have constantSum := (PoissonizedWalk.weights_hasSum
    (time * xiNativeFiniteJumpRate system level resistanceRate normalization)).smul_const
      (xiFiniteSpeedL2 system mass level (fun _ => 1))
  simp only [xiNativeRandomWalk_powers_preserve_one system rulesConnected mass level
    rulesLoopless rulesUnique plantingNonadjacent] at walkSum
  simp only [one_smul] at constantSum
  rw [xiNativePoissonizedWalk_eq_semigroup]
  exact walkSum.unique constantSum

theorem xiNativePoissonizedWalk_strong_limit (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector))) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass))),
      ∀ (time : ℝ≥0)
        (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass)),
      core.Strong forcing target →
      core.Strong (fun level => xiNativePoissonizedWalk system rulesConnected mass level
        resistanceRate normalization time (forcing level))
        (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable
          originalDense time target) := by
  simpa only [xiNativePoissonizedWalk_eq_semigroup] using
    xiNativeFiniteSemigroup_strong_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive
      normalizedConvergence

theorem exists_xiNativePoissonizedWalkStrong_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
        (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive
      let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
        intro sequence energyCauchy ambientZero
        exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
          mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
          (by simpa using ambientZero.norm)
      ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass))),
        ∀ (time : ℝ≥0)
          (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
          (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass)),
        core.Strong forcing target →
        core.Strong (fun level => xiNativePoissonizedWalk system rulesConnected mass level
          resistanceRate normalization time (forcing level))
          (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable
            originalDense time target) := by
  classical
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
      originalDense, originalNonnegative⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, originalDense, ?_⟩
  exact xiNativePoissonizedWalk_strong_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense


end
end EIGS

#print axioms IGS.Sec31.PoissonizedWalk.weight_nonnegative
#print axioms IGS.Sec31.PoissonizedWalk.weights_hasSum
#print axioms IGS.Sec31.PoissonizedWalk.weight_zero_parameter
#print axioms IGS.Sec31.PoissonizedWalk.exponential_identity
#print axioms IGS.Sec31.PoissonizedWalk.operator_hasSum
#print axioms IGS.Sec31.PoissonizedWalk.apply_hasSum
#print axioms EIGS.xiNativeFiniteJumpRate_nonnegative
#print axioms EIGS.xiNativeFiniteGenerator_eq_jumpRate
#print axioms EIGS.xiNativeFiniteSemigroup_poisson_hasSum
#print axioms EIGS.xiNativePoissonizedWalk_eq_semigroup
#print axioms EIGS.xiNativeFiniteSemigroup_poisson_apply_hasSum
#print axioms EIGS.xiNativePoissonizedWalk_weights_nonnegative
#print axioms EIGS.xiNativePoissonizedWalk_zero
#print axioms EIGS.xiNativePoissonizedWalk_of_zero_rate
#print axioms EIGS.xiNativeRandomWalk_preserves_nonnegative
#print axioms EIGS.xiNativeRandomWalk_powers_preserve_nonnegative
#print axioms EIGS.xiNativeRandomWalk_preserves_one
#print axioms EIGS.xiNativeRandomWalk_powers_preserve_one
#print axioms EIGS.xiNativePoissonizedWalk_preserves_one

#print axioms EIGS.xiNativePoissonizedWalk_strong_limit
#print axioms EIGS.exists_xiNativePoissonizedWalkStrong_of_rules
