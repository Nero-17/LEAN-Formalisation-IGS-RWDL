import RequestProject.Section31.AnchoredTraceEnergyHilbert
import RequestProject.Section31.EIGSSkeletonAnchoredCompleteness

/-! The actual EIGS finite-energy space, with one anchored value, is a
Hilbert space. Both inputs to the general construction are proved from the
actual networks: weighted trace monotonicity and finite-network evaluation
bounds. The subspace vanishing at the anchor is complete for the energy norm.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31
noncomputable section
variable {K : ℕ}

abbrev XiAnchoredEnergyHilbert (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (anchor : XiVertexUnion system) :=
  AnchoredTraceEnergySpace
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
    (xiUnionWeightedNetwork_energy_increasing_of_eigenpair system rulesConnected resistanceRate
      ratePositive resistanceVector vectorPositive eigenpair) anchor
    (exists_xiWeightedEnergy_anchored_evaluation system rulesConnected resistanceRate
      ratePositive resistanceVector vectorPositive anchor)

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (anchor : XiVertexUnion system)

theorem xiAnchoredEnergyHilbert_norm_sq
    (values : XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor) :
    ‖values‖ ^ 2 =
      (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        values.value.val).toReal + (values.value.val anchor) ^ 2 :=
  AnchoredTraceEnergySpace.norm_sq _ _ _ _ values

def xiAnchoredEnergyEvaluation (vertex : XiVertexUnion system) :
    XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor →L[ℝ] ℝ := by
  let evaluation : XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor →ₗ[ℝ] ℝ :=
    { toFun := fun values => values.value.val vertex
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let evaluationBound := exists_xiWeightedEnergy_anchored_evaluation system rulesConnected
    resistanceRate ratePositive resistanceVector vectorPositive anchor vertex
  let coefficient := Classical.choose evaluationBound
  have coefficientPositive := (Classical.choose_spec evaluationBound).1
  have control := (Classical.choose_spec evaluationBound).2
  refine evaluation.mkContinuous (Real.sqrt coefficient) ?_
  intro values
  change |values.value.val vertex| ≤ Real.sqrt coefficient * ‖values‖
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt coefficientPositive.le,
    xiAnchoredEnergyHilbert_norm_sq]
  exact control values.value

@[simp] theorem xiAnchoredEnergyEvaluation_apply (vertex : XiVertexUnion system)
    (values : XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor) :
    xiAnchoredEnergyEvaluation system rulesConnected resistanceRate ratePositive resistanceVector
      vectorPositive eigenpair anchor vertex values = values.value.val vertex := rfl

def xiZeroAnchoredEnergyDomain : Submodule ℝ
    (XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor) :=
  (xiAnchoredEnergyEvaluation system rulesConnected resistanceRate ratePositive resistanceVector
    vectorPositive eigenpair anchor anchor).ker

instance xiZeroAnchoredEnergyDomain_completeSpace : CompleteSpace
    (xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor) := by
  exact (xiAnchoredEnergyEvaluation system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair anchor anchor).isComplete_ker.completeSpace_coe

theorem xiZeroAnchoredEnergyDomain_norm_sq
    (values : xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor) :
    ‖values‖ ^ 2 =
      (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        values.val.value.val).toReal := by
  have vanishes : values.val.value.val anchor = 0 := values.property
  change ‖values.val‖ ^ 2 = _
  rw [xiAnchoredEnergyHilbert_norm_sq, vanishes, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]

end
end EIGS

#print axioms EIGS.xiAnchoredEnergyHilbert_norm_sq
#print axioms EIGS.xiAnchoredEnergyEvaluation
#print axioms EIGS.xiZeroAnchoredEnergyDomain_completeSpace
#print axioms EIGS.xiZeroAnchoredEnergyDomain_norm_sq
