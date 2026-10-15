import RequestProject.Section31.EIGSUVFlowerRuleResistance
import RequestProject.Section31.EIGSUVFlowerRuleConnectivity
import RequestProject.Section31.EIGSUVFlowerMassSpectrum
import RequestProject.Section2ResistanceSpectralRadius

/-! The actual unequal-path flower renormalization map and its canonical
resistance rate. Its admissible fractal rules have rate at least one,
with equality precisely for the (2,2)-flower. -/

namespace EIGS
noncomputable section
open scoped Classical

theorem uvFlowerSystem_Psi (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength)
    (resistances : Fin 1 → ℝ) (nonnegative : 0 ≤ resistances) :
    ((uvFlowerSystem firstLength secondLength).ruleFamily
      (uvFlowerSystem_connected firstLength secondLength firstPositive secondPositive)).Psi resistances =
        fun _ => uvFlowerRuleResistance firstLength secondLength * resistances 0 := by
  funext colour
  have colourZero : colour = 0 := Subsingleton.elim _ _
  subst colour
  exact uvFlowerRule_effRes firstLength secondLength firstPositive secondPositive _ resistances nonnegative

theorem uvFlowerSystem_resistanceSpectralRadius (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength) :
    (uvFlowerSystem firstLength secondLength).resistanceSpectralRadius
      (uvFlowerSystem_connected firstLength secondLength firstPositive secondPositive)
      (uvFlowerSystem_distancePositive firstLength secondLength) = uvFlowerRuleResistance firstLength secondLength := by
  symm
  apply (uvFlowerSystem firstLength secondLength).resistanceSpectralRadius_eq_of_positive_eigenpair
    (uvFlowerSystem_connected firstLength secondLength firstPositive secondPositive)
    (uvFlowerSystem_distancePositive firstLength secondLength)
    (div_pos (mul_pos (Nat.cast_pos.mpr firstPositive) (Nat.cast_pos.mpr secondPositive))
      (add_pos (Nat.cast_pos.mpr firstPositive) (Nat.cast_pos.mpr secondPositive)))
    (vector := fun _ => 1) (fun _ => zero_lt_one)
  rw [uvFlowerSystem_Psi firstLength secondLength firstPositive secondPositive _ (fun _ => zero_le_one)]
  funext colour
  simp [uvFlowerRuleResistance]

theorem uvFlowerRuleResistance_ge_one (firstLength secondLength : ℕ)
    (firstAtLeastTwo : 2 ≤ firstLength) (secondAtLeastTwo : 2 ≤ secondLength) :
    1 ≤ uvFlowerRuleResistance firstLength secondLength := by
  have firstBound : (2 : ℝ) ≤ firstLength := by exact_mod_cast firstAtLeastTwo
  have secondBound : (2 : ℝ) ≤ secondLength := by exact_mod_cast secondAtLeastTwo
  have denominatorPositive : 0 < (firstLength : ℝ) + secondLength := by linarith
  unfold uvFlowerRuleResistance
  apply (le_div_iff₀ denominatorPositive).2
  nlinarith [mul_nonneg (sub_nonneg.mpr firstBound) (sub_nonneg.mpr secondBound)]

theorem uvFlowerRuleResistance_eq_one_iff (firstLength secondLength : ℕ)
    (firstAtLeastTwo : 2 ≤ firstLength) (secondAtLeastTwo : 2 ≤ secondLength) :
    uvFlowerRuleResistance firstLength secondLength = 1 ↔ firstLength = 2 ∧ secondLength = 2 := by
  have firstBound : (2 : ℝ) ≤ firstLength := by exact_mod_cast firstAtLeastTwo
  have secondBound : (2 : ℝ) ≤ secondLength := by exact_mod_cast secondAtLeastTwo
  constructor
  · intro equality
    have denominatorNonzero : (firstLength : ℝ) + secondLength ≠ 0 := by linarith
    have productEquality : (firstLength : ℝ) * secondLength = (firstLength : ℝ) + secondLength := by
      have product := (div_eq_iff denominatorNonzero).1 equality
      simpa only [one_mul] using product
    have firstEquality : (firstLength : ℝ) = 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr firstBound) (sub_nonneg.mpr secondBound)]
    have secondEquality : (secondLength : ℝ) = 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr firstBound) (sub_nonneg.mpr secondBound)]
    exact ⟨by exact_mod_cast firstEquality, by exact_mod_cast secondEquality⟩
  · rintro ⟨rfl, rfl⟩
    norm_num [uvFlowerRuleResistance]

theorem uvFlowerSystem_resistanceSpectralRadius_ge_one (firstLength secondLength : ℕ)
    (firstAtLeastTwo : 2 ≤ firstLength) (secondAtLeastTwo : 2 ≤ secondLength) :
    1 ≤ (uvFlowerSystem firstLength secondLength).resistanceSpectralRadius
      (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega))
      (uvFlowerSystem_distancePositive firstLength secondLength) := by
  rw [uvFlowerSystem_resistanceSpectralRadius firstLength secondLength (by omega) (by omega)]
  exact uvFlowerRuleResistance_ge_one firstLength secondLength firstAtLeastTwo secondAtLeastTwo

theorem uvFlowerSystem_mass_times_resistance (firstLength secondLength : ℕ)
    (firstPositive : 0 < firstLength) (secondPositive : 0 < secondLength) :
    realMatrixSpectralRadius (massMatrixR (uvFlowerSystem firstLength secondLength).toRuleData) *
      (uvFlowerSystem firstLength secondLength).resistanceSpectralRadius
        (uvFlowerSystem_connected firstLength secondLength firstPositive secondPositive)
        (uvFlowerSystem_distancePositive firstLength secondLength) = (firstLength : ℝ) * secondLength := by
  rw [uvFlowerSystem_massSpectralRadius,
    uvFlowerSystem_resistanceSpectralRadius firstLength secondLength firstPositive secondPositive]
  unfold uvFlowerRuleResistance
  have denominatorNonzero : (firstLength : ℝ) + secondLength ≠ 0 :=
    (add_pos (Nat.cast_pos.mpr firstPositive) (Nat.cast_pos.mpr secondPositive)).ne'
  field_simp [denominatorNonzero]

end
end EIGS

#print axioms EIGS.uvFlowerSystem_Psi
#print axioms EIGS.uvFlowerSystem_resistanceSpectralRadius
#print axioms EIGS.uvFlowerRuleResistance_ge_one
#print axioms EIGS.uvFlowerRuleResistance_eq_one_iff
#print axioms EIGS.uvFlowerSystem_resistanceSpectralRadius_ge_one
#print axioms EIGS.uvFlowerSystem_mass_times_resistance
