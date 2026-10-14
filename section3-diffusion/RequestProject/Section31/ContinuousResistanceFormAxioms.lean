import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! A resistance form on continuous functions, including the complete
quotient by constants. The quotient is certified by a surjective linear map
onto a complete energy Hilbert space, with exactly the constant functions as
kernel and energy equal to norm squared. The remaining fields are the finite
interpolation, finite sharp resistance, and Markov axioms. -/

namespace IGS.Sec31
noncomputable section

structure ContinuousResistanceFormAxioms
    (Space Hilbert : Type*) [MetricSpace Space] [CompactSpace Space]
    [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert] [CompleteSpace Hilbert]
    (domain : Submodule ℝ C(Space, ℝ)) (energy : QuadraticForm ℝ domain)
    (resistance : Space → Space → ℝ) : Prop where
  constant_domain : ∀ constant : ℝ, ContinuousMap.const Space constant ∈ domain
  energy_nonnegative : ∀ function : domain, 0 ≤ energy function
  energy_zero_iff_constant : ∀ function : domain,
    energy function = 0 ↔ ∃ constant : ℝ, ∀ point, function.val point = constant
  complete_quotient : ∃ normalization : domain →ₗ[ℝ] Hilbert,
    Function.Surjective normalization ∧
    (∀ function, ‖normalization function‖ ^ 2 = energy function) ∧
    (∀ function, normalization function = 0 ↔ ∃ constant : ℝ, ∀ point, function.val point = constant)
  finite_interpolation : ∀ points : Finset Space,
    Function.Surjective (fun function : domain => fun vertex : points => function.val vertex.val)
  resistance_nonnegative : ∀ first second, 0 ≤ resistance first second
  sharp_energy_bound : ∀ first second (function : domain),
    (function.val first - function.val second) ^ 2 ≤ resistance first second * energy function
  attaining_function : ∀ first second, ∃ function : domain,
    function.val first - function.val second = resistance first second ∧
    energy function = resistance first second
  normal_contraction : ∀ contraction : ℝ → ℝ,
    (∀ first second, |contraction first - contraction second| ≤ |first - second|) →
    ∀ function : domain, ∃ contracted : domain,
      (∀ point, contracted.val point = contraction (function.val point)) ∧ energy contracted ≤ energy function

end
end IGS.Sec31

#print axioms IGS.Sec31.ContinuousResistanceFormAxioms
#print axioms IGS.Sec31.ContinuousResistanceFormAxioms.mk
