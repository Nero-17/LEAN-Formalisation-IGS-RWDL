import RequestProject.Section31.EIGSAnchoredEnergyHilbert
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Positive-part truncation about any skeleton vertex, followed by the unique
constant shift restoring the original anchor. This acts in the actual complete
pure-energy space and decreases its norm. It is the concrete Markov operation
needed to prove the triangle inequality for resistance itself.
Candidate source: compilation is not claimed. -/

namespace IGS.Sec31

theorem shifted_positive_part_contraction (pivot offset : ℝ) :
    ∀ first second : ℝ,
      |(max (first - pivot) 0 - offset) - (max (second - pivot) 0 - offset)| ≤ |first - second| := by
  intro first second
  have bound := ((LipschitzWith.id : LipschitzWith 1 (fun value : ℝ => value)).max_const 0).dist_le_mul
    (first - pivot) (second - pivot)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at bound
  convert bound using 1 <;> congr 1 <;> ring

end IGS.Sec31

namespace EIGS
open IGS.Sec31
noncomputable section
variable {K : ℕ}

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (anchor : XiVertexUnion system)

def xiZeroAnchoredPositivePart
    (values : xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor) (pivot : XiVertexUnion system) :
    xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor := by
  let contraction := fun value : ℝ => max (value - values.val.value.val pivot) 0 -
    max (values.val.value.val anchor - values.val.value.val pivot) 0
  have finite : contraction ∘ values.val.value.val ∈
      xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive :=
    traceEnergyDomain_comp _ contraction (shifted_positive_part_contraction _ _)
      values.val.value.property
  refine ⟨⟨⟨contraction ∘ values.val.value.val, finite⟩⟩, ?_⟩
  change max (values.val.value.val anchor - values.val.value.val pivot) 0 -
    max (values.val.value.val anchor - values.val.value.val pivot) 0 = 0
  exact sub_self _

@[simp] theorem xiZeroAnchoredPositivePart_apply
    (values : xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor) (pivot vertex : XiVertexUnion system) :
    (xiZeroAnchoredPositivePart system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor values pivot).val.value.val vertex =
    max (values.val.value.val vertex - values.val.value.val pivot) 0 -
      max (values.val.value.val anchor - values.val.value.val pivot) 0 := rfl

theorem xiZeroAnchoredPositivePart_norm_sq_le
    (values : xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor) (pivot : XiVertexUnion system) :
    ‖xiZeroAnchoredPositivePart system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor values pivot‖ ^ 2 ≤ ‖values‖ ^ 2 := by
  rw [xiZeroAnchoredEnergyDomain_norm_sq, xiZeroAnchoredEnergyDomain_norm_sq]
  apply ENNReal.toReal_mono
    ((xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).1
      values.val.value.property)
  exact extendedTraceEnergy_comp_le _ _ (shifted_positive_part_contraction _ _) values.val.value.val

end
end EIGS

#print axioms IGS.Sec31.shifted_positive_part_contraction
#print axioms EIGS.xiZeroAnchoredPositivePart_norm_sq_le
